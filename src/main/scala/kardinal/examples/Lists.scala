package kardinal.examples

import kardinal.core._
import kardinal.core.dsl._

object Lists {
  // Unsorted lists of length `s`
  def exact_unsorted(s: Int, range: Range): Enum[List[Int]] =
    rec[Int, List[Int]](true) { case (size, self) =>
      if (size == 0)
        Nil
      else
        (range * self(size - 1)) map { case (v, tail) => v :: tail }
    } .apply(s)

  // Sorted lists of size `s`
  def exact_sorted(s: Int, r: Range): Enum[List[Int]] =
    rec[(Int, Range), List[Int]](true) { case ((size, range), self) =>
      if (size == 0)
        Nil
      else
        range flatMapFinite (v =>
          v * self((size - 1, v+1 until range.end))
        ) map { case (v, tail) => v :: tail }
    } .apply(s, r)

  // All elements of size up to `s`
  def upto(f: (Int, Range) => Enum[List[Int]])(s: Int, range: Range): Enum[List[Int]] =
    (0 to s) flatMapFinite (f(_, range))

  def demo(): Unit = {
    val N: Int = 4
    val Vs: Range = 0 until N

    def runOne[T](name: String, gen: (Int, Range) => Enum[T]): Unit = {
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