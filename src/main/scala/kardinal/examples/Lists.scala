package kardinal.examples

import kardinal.core._
import kardinal.core.dsl._

object Lists {
  // import scala.language.implicitConversions

  def exact_unsorted(s: Int, range: Range): Enum[List[Int]] =
    rec[Int, List[Int]](true) { case (size, self) =>
      if (size == 0)
        enumFromSingleton(Nil)
      else {
        val pairs = enumFromRange(range) * (enumFromSingleton(size - 1) bind self)
        pairs map { case (v, tail) => v :: tail }
      }
    } .apply(s)

  def exact_sorted(s: Int, r: Range): Enum[List[Int]] =
    rec[(Int, Range), List[Int]](true) { case ((size, range), self) =>
      if (size == 0)
        enumFromSingleton(Nil)
      else
        enumFromRange(range) bind lift(true)(v =>
          enumFromSingleton(v) * self((size - 1, v+1 until range.end))
        ) map { case (v, tail) => v :: tail }
    } .apply(s, r)

  def upto(f: (Int, Range) => Enum[List[Int]])(s: Int, range: Range): Enum[List[Int]] =
    enumFromRange(0 to s) bind lift(true)(f(_, range))

  def demo(): Unit = {
    def runOne[T](name: String, gen: (Int, Range) => Enum[T]): Unit = {
      val N: Int = 10
      val Vs: Range = 0 until N+1
      val lists = gen(N, Vs)
      println(s" == $name ==")
      println(s"# of lists: ${lists.size}")
      // lists.iterator.foreach(list => println(s"  - $list"))
      println("")
    }

    runOne("exact, unsorted", exact_unsorted)
    runOne("upto, unsorted", upto(exact_unsorted))
    runOne("exact, sorted", exact_sorted)
    runOne("upto, sorted", upto(exact_sorted))
  }
}