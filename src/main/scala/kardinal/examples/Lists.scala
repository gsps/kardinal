package kardinal.examples

import kardinal.core._
import kardinal.core.dsl._

object Lists {
  // Unsorted lists of length `s`
  def exact_unsorted(s: Int, range: Range): Enum[List[Int]] =
    rec[Int, List[Int]] { case (size, self) =>
      if (size == 0)
        Nil
      else
        (range * self(size - 1)) map { case (v, tail) => v :: tail }
    } .apply(s)

  // Sorted lists of size `s`
  def exact_sorted(s: Int, r: Range): Enum[List[Int]] =
    rec[(Int, Range), List[Int]] { case ((size, range), self) =>
      if (size == 0)
        Nil
      else
        range flatMapEnum (v =>
          enumFromSingleton(v) * self((size - 1, v+1 until range.end))
        ) map { case (v, tail) => v :: tail }
    } .apply(s, r)

  // All lists of size up to `s`
  def upto(f: (Int, Range) => Enum[List[Int]])(s: Int, range: Range): Enum[List[Int]] =
    (0 to s) flatMapEnum (f(_, range))

  def demo(): Unit = {
    val N: Int = 15
    val Vs: Range = 0 until N

    def runOne(name: String, gen: (Int, Range) => Enum[List[Int]]): Unit = {
      val lists = gen(N, Vs)
      println(s" == $name ==")
      println(s"# of lists: ${lists.size}")
      // lists.iterator.foreach(list => println(s"  - $list"))
      println("")
    }

    def inspectOne(gen: (Int, Range) => Enum[List[Int]]): Unit = {
      val I = 10
      val lists = gen(N, Vs)
      println(s"lists($I): ${lists(I)}")
      println(s"       <-> ${lists.indexTree(I)}")
      println("")
    }

    runOne("exact, unsorted", exact_unsorted)
    runOne("upto, unsorted", upto(exact_unsorted))
    runOne("exact, sorted", exact_sorted)
    runOne("upto, sorted", upto(exact_sorted))

    // inspectOne(upto(exact_unsorted))
    // println(s"            ${(math.pow(Vs.length, (N + 1)).toLong - 1) / (Vs.length - 1)}")
  }


  import org.scalameter.api._
  import org.scalameter.picklers.Implicits._

  object Benchmark extends Bench[Double] {
    implicit val order = Ordering.Double.IeeeOrdering
    lazy val executor = LocalExecutor(
      new Executor.Warmer.Default,
      Aggregator.min[Double],
      measurer)
    lazy val measurer = new Measurer.Default
    lazy val reporter = Reporter.Composite(
      new RegressionReporter(
        RegressionReporter.Tester.Accepter(),
        RegressionReporter.Historian.ExponentialBackoff()),
      HtmlReporter(true)
    )
    lazy val persistor = new GZIPJSONSerializationPersistor("target/results")

    val sizes18 = Gen.range("size")(1, 34, 1)
    val sizes15 = Gen.range("size")(1, 15, 1)
    val gen = upto(exact_unsorted)(_, _)

    performance of "Unsorted bit-strings up to N" in {
      measure method "count" config (
        exec.minWarmupRuns -> 100,
        exec.maxWarmupRuns -> 100,
        exec.benchRuns -> 50
      ) in {
        def run = using(sizes18) in { s => gen(s, 0 until 2).size }
        measure method "naive" in run
      }

      // measure method "enumerate" in {
      //   using(sizes15) in { s => gen(s, 0 until 2).iterator.foreach(_ => ()) }
      // }
    }
  }
}