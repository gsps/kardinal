package kardinal.core

import scala.reflect._
import scala.collection.mutable.{Map => MutableMap}

// == First-order enumerators ==

sealed abstract class Enum[T : ClassTag] extends EnumOps[T] {
  def apply(index: Index): T
  def size: Size

  def indexTree(index: Index): IndexTree

  def iterator: Iterator[T]
}

case class EnumerationException[T : ClassTag](enum: Enum[T], index: Index)
    extends Exception(
      s"Index out-of-bounds: $index / ${enum.size}",
      null
    )

case class Sum[T : ClassTag](e1: Enum[T], e2: Enum[T]) extends Enum[T] {
  val pairing: Pairing = SumPairing(e1, e2)
  def apply(index: Index) = {
    val (eIndex, vIndex) = pairing.decompose(index)
    assert(eIndex == 0 || eIndex == 1)
    if (eIndex == 0) e1(vIndex) else e2(vIndex)
  }
  lazy val size = e1.size + e2.size

  def indexTree(index: Index): IndexTree = {
    val (eIndex, vIndex) = pairing.decompose(index)
    val vTree = if (eIndex == 0) e1.indexTree(vIndex) else e2.indexTree(vIndex)
    Decomposed(pairing, AtomicIndex(eIndex), vTree)
  }

  def iterator = e1.iterator ++ e2.iterator
}

case class Product[T1 : ClassTag, T2 : ClassTag](e1: Enum[T1], e2: Enum[T2]) extends Enum[(T1, T2)] {
  val pairing: Pairing = ProductPairing(e1, e2)
  def apply(index: Index) = {
    val (index1, index2) = pairing.decompose(index)
    (e1(index1), e2(index2))
  }
  lazy val size = e1.size * e2.size

  def indexTree(index: Index): IndexTree = {
    val (index1, index2) = pairing.decompose(index)
    Decomposed(pairing, e1.indexTree(index1), e2.indexTree(index2))
  }

  private abstract class ProductIterator[S : ClassTag, L : ClassTag, T <: Tuple2[_, _] : ClassTag](
      eShort: Enum[S],
      eLong: Enum[L]
  ) extends Iterator[T] {
    private val short: Array[S] = eShort.iterator.toArray
    private val itLong: Iterator[L] = eLong.iterator
    private val row: Array[T] = new Array(short.size)
    private var rowOffset: Int = row.size

    protected def buildTuple(s: S, l: L): T

    def hasNext: Boolean = rowOffset < row.size || row.size > 0 && itLong.hasNext
    def next(): T =
      if (rowOffset < row.size) {
        val value = row(rowOffset)
        rowOffset += 1
        value
      } else if (row.size > 0 && itLong.hasNext) {
        val l: L = itLong.next()
        (0 until row.size) foreach { i =>
          row(i) = buildTuple(short(i), l)
        }
        rowOffset = 1
        row(0)
      } else {
        throw new NoSuchElementException()
      }
  }
  private class Product12Iterator extends ProductIterator[T1, T2, (T1, T2)](e1, e2) {
    protected def buildTuple(s: T1, l: T2) = (s, l)
  }
  private class Product21Iterator extends ProductIterator[T2, T1, (T1, T2)](e2, e1) {
    protected def buildTuple(s: T2, l: T1) = (l, s)
  }
  def iterator = if (e1.size < e2.size) new Product12Iterator else new Product21Iterator
}

case class Map[S : ClassTag, T : ClassTag](e: Enum[S], f: S => T) extends Enum[T] {
  def apply(index: Index) = f(e(index))
  def size = e.size

  def indexTree(index: Index): IndexTree = e.indexTree(index)

  def iterator = e.iterator.map(f)
}

case class Filter[T : ClassTag](e: Enum[T], f: T => Boolean) extends Enum[T] {
  // lazy val values: Array[T] = e.iterator.filter(f).toArray

  def apply(index: Index): T =
    // if (index < values.size)
    //   values(index.toInt)
    // else
    //   throw EnumerationException(this, index)
    ???
  lazy val size = e.iterator.count(f)

  def indexTree(index: Index): IndexTree = ???

  def iterator = e.iterator.filter(f)
}

case class Bind[V : ClassTag, T : ClassTag](e: Enum[V], ed: Depend[V, T]) extends Enum[T] {
  def innerSizes: Iterator[Size] = e.iterator.map(ed.apply(_).size)

  lazy val pairing: Pairing = LinearK(innerSizes.iterator)

  def apply(index: Index): T = {
    val (index1, index2) = pairing.decompose(index)
    val v = e(index1)
    ed(v)(index2)
  }
  lazy val size: Size = innerSizes.sum

  def indexTree(index: Index): IndexTree = {
    val (index1, index2) = pairing.decompose(index)
    val v = e(index1)
    Decomposed(pairing, e.indexTree(index1), ed(v).indexTree(index2))
  }

  def iterator = e.iterator.flatMap(ed.apply(_).iterator)
}

case class Cached[T : ClassTag](e: Enum[T]) extends Enum[T] {
  lazy val values: Array[T] = e.iterator.toArray

  def apply(index: Index): T =
    if (index < values.size)
      values(index.toInt)
    else
      throw EnumerationException(this, index)
  lazy val size = values.size

  def indexTree(index: Index): IndexTree = ???

  def iterator = values.iterator
}

// == Dependent enumerators ==

// TODO: Make factories for Depend[V, T] take an explicit flag denoting cacheability
abstract class Depend[V, T : ClassTag] {
  private val cache: MutableMap[V, Enum[T]] = MutableMap.empty
  protected def compute(v: V): Enum[T]
  // def apply(v: V): Enum[T] = cache.getOrElseUpdate(v, compute(v))
  def apply(v: V): Enum[T] = cache.getOrElseUpdate(v, Cached(compute(v)))
}

// case class DSum[V, T](ed1: Depend[V, T], ed2: Depend[V, T]) extends Depend[V, T]

// case class DProduct[V, T1, T2](ed1: Depend[V, T1], ed2: Depend[V, T2]) extends Depend[V, (T1, T2)]

// case class DMap[V, W, T](ed: Depend[W, T], f: V => W) extends Depend[V, T]

case class DLift[V, T : ClassTag](f: V => Enum[T]) extends Depend[V, T] {
  protected def compute(v: V): Enum[T] = f(v)
}

case class DRec[V, T : ClassTag](f: (V, Depend[V, T]) => Enum[T]) extends Depend[V, T] {
  protected def compute(v: V): Enum[T] = f(v, this)
}

// == Atomic first-order enumerators ==

abstract class AtomicEnum[T : ClassTag] extends Enum[T]

case class SingletonAtomicEnum[T : ClassTag](value: T) extends Enum[T] {
  def apply(index: Index): T =
    if (index == 0) value else throw EnumerationException(this, index)
  val size: Size = 1

  def indexTree(index: Index): IndexTree = AtomicIndex(index)

  def iterator = Iterator.single(value)
}
case class RangeAtomicEnum(range: Range) extends Enum[Int] {
  def apply(index: Index): Int =
    if (index < size) range(index.toInt) else throw EnumerationException(this, index)
  val size: Size = range.size

  def indexTree(index: Index): IndexTree = AtomicIndex(index)

  def iterator = range.iterator
}

// == DSL helpers ==

abstract class EnumOps[T1 : ClassTag] { self: Enum[T1] =>
  def +(e2: Enum[T1]): Enum[T1] = Sum(this, e2)
  def *[T2 : ClassTag](e2: Enum[T2]): Enum[(T1, T2)] = Product(this, e2)
  def map[U : ClassTag](f: T1 => U): Enum[U] = Map(this, f)
  def filter(f: T1 => Boolean): Enum[T1] = Filter(this, f)
  def bind[U : ClassTag](ed: Depend[T1, U]): Enum[U] = Bind(this, ed)
  def flatMapEnum[U : ClassTag](f: T1 => Enum[U]): Enum[U] = Bind(this, dsl.lift(f))
}

// class DependOps[V, T1](ed1: Depend[V, T1]) {
//   def +(ed2: Depend[V, T1]): Depend[V, T1] = DSum(ed1, ed2)
//   def *[T2](ed2: Depend[V, T2]): Depend[V, (T1, T2)] = DProduct(ed1, ed2)
//   def map[U](f: U => V): Depend[U, T1] = DMap(ed1, f)
// }

object dsl {
  def lift[V, T : ClassTag](f: V => Enum[T]): Depend[V, T] =
    DLift(f)
  def rec[V, T : ClassTag](f: (V, Depend[V, T]) => Enum[T]): Depend[V, T] =
    DRec(f)

  implicit def enumFromSingleton[T : ClassTag](value: T): Enum[T] = SingletonAtomicEnum(value)
  implicit def enumFromRange(range: Range): Enum[Int] = RangeAtomicEnum(range)
}
