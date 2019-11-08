package kardinal.core

import scala.collection.mutable.{Map => MutableMap}

// == First-order enumerators ==

sealed trait Enum[T] extends EnumOps[T] {
  def apply(index: Index): T
  def hasDefiniteSize: Boolean
  def size: Size

  def indexTree(index: Index): IndexTree

  def iterator: Iterator[T] = new EnumIterator(this, 0)

  def checkIndex(index: Index) = {
    // assert(0 <= index && !hasDefiniteSize || index < size,
    //   s"Index out-of-bounds: $index not in [0, $size[")
  }
}

case class EnumerationException[T](enum: Enum[T], index: Index)
    extends Exception(
      s"Index out-of-bounds: $index / ${if (enum.hasDefiniteSize) enum.size.toString else "???"}",
      null
    )

class EnumIterator[T](private val enum: Enum[T], private var index: Index) extends Iterator[T] {
  private var _next: T = fetchNext()
  private def fetchNext(): T =
    try {
      val element = enum(index)
      index += 1
      element
    } catch {
      case ex: EnumerationException[T] =>
        null.asInstanceOf[T]
    }

  def hasNext: Boolean = _next != null
  def next(): T =
    if (hasNext) {
      val element = _next
      _next = fetchNext()
      element
    } else {
      throw new NoSuchElementException()
    }
}

case class Sum[T](e1: Enum[T], e2: Enum[T]) extends Enum[T] {
  val pairing: Pairing = SumPairing(e1, e2)
  def apply(index: Index) = {
    checkIndex(index)
    val (eIndex, vIndex) = pairing.decompose(index)
    assert(eIndex == 0 || eIndex == 1)
    if (eIndex == 0) e1(vIndex) else e2(vIndex)
  }
  val hasDefiniteSize = e1.hasDefiniteSize && e2.hasDefiniteSize
  lazy val size = e1.size + e2.size

  def indexTree(index: Index): IndexTree = {
    val (eIndex, vIndex) = pairing.decompose(index)
    val vTree = if (eIndex == 0) e1.indexTree(vIndex) else e2.indexTree(vIndex)
    Decomposed(pairing, AtomicIndex(eIndex), vTree)
  }
}

case class Product[T1, T2](e1: Enum[T1], e2: Enum[T2]) extends Enum[(T1, T2)] {
  val pairing: Pairing = ProductPairing(e1, e2)
  def apply(index: Index) = {
    checkIndex(index)
    val (index1, index2) = pairing.decompose(index)
    (e1(index1), e2(index2))
  }
  val hasDefiniteSize = e1.hasDefiniteSize && e2.hasDefiniteSize
  lazy val size = e1.size * e2.size

  def indexTree(index: Index): IndexTree = {
    val (index1, index2) = pairing.decompose(index)
    Decomposed(pairing, e1.indexTree(index1), e2.indexTree(index2))
  }
}

case class Map[S, T](e: Enum[S], f: S => T) extends Enum[T] {
  def apply(index: Index) = {
    checkIndex(index)
    f(e(index))
  }
  def hasDefiniteSize = e.hasDefiniteSize
  def size = e.size

  def indexTree(index: Index): IndexTree = e.indexTree(index)
}

// case class Filter[T](e: Enum[T], f: T => Boolean) extends Enum[T]

case class Bind[V, T](e: Enum[V], ed: Depend[V, T]) extends Enum[T] {
  // def innerSizesIterator: Iterator[Size] = e.iterator.map(ed.apply(_).size)
  // lazy val innerSizes: LazyList[Size] = LazyList.from(e.iterator.map(ed.apply(_).size))
  def innerSizes: Iterator[Size] = e.iterator.map(ed.apply(_).size)

  lazy val pairing: Pairing =
    if (innerEnumsHaveDefiniteSizes) LinearK(innerSizes.iterator)
    else if (e.hasDefiniteSize) DivMod2(e.size)
    else Cantor2

  def apply(index: Index): T = {
    checkIndex(index)
    val (index1, index2) = pairing.decompose(index)
    val v = e(index1)
    ed(v)(index2)
  }
  def innerEnumsHaveDefiniteSizes = ed.innerEnumsHaveDefiniteSizes
  // def innerEnumsHaveDefiniteSizes = e.iterator.forall(ed(_).hasDefiniteSize)
  lazy val hasDefiniteSize = e.hasDefiniteSize && innerEnumsHaveDefiniteSizes
  lazy val size: Size = {
    assert(hasDefiniteSize)
    innerSizes.sum
  }

  def indexTree(index: Index): IndexTree = {
    val (index1, index2) = pairing.decompose(index)
    val v = e(index1)
    Decomposed(pairing, e.indexTree(index1), ed(v).indexTree(index2))
  }
}

// == Dependent enumerators ==

// TODO: Make factories for Depend[V, T] take an explicit flag denoting cacheability
trait Depend[V, T] {
  private val cache: MutableMap[V, Enum[T]] = MutableMap.empty
  protected def compute(v: V): Enum[T]
  def apply(v: V): Enum[T] = cache.getOrElseUpdate(v, compute(v))
  def innerEnumsHaveDefiniteSizes: Boolean
}

// case class DSum[V, T](ed1: Depend[V, T], ed2: Depend[V, T]) extends Depend[V, T]

// case class DProduct[V, T1, T2](ed1: Depend[V, T1], ed2: Depend[V, T2]) extends Depend[V, (T1, T2)]

// case class DMap[V, W, T](ed: Depend[W, T], f: V => W) extends Depend[V, T]

case class DLift[V, T](
    innerEnumsHaveDefiniteSizes: Boolean,
    f: V => Enum[T]
) extends Depend[V, T] {
  protected def compute(v: V): Enum[T] = f(v)
}

case class DRec[V, T](
    innerEnumsHaveDefiniteSizes: Boolean,
    f: (V, Depend[V, T]) => Enum[T]
) extends Depend[V, T] {
  protected def compute(v: V): Enum[T] = f(v, this)
}

// == Atomic first-order enumerators ==

trait AtomicEnum[T] extends Enum[T]

case class SingletonAtomicEnum[T](value: T) extends Enum[T] {
  def apply(index: Index): T =
    if (index == 0) value else throw EnumerationException(this, index)
  val hasDefiniteSize = true
  val size: Size = 1

  def indexTree(index: Index): IndexTree = AtomicIndex(index)
}
case class RangeAtomicEnum(range: Range) extends Enum[Int] {
  def apply(index: Index): Int =
    if (index < size) range(index.toInt) else throw EnumerationException(this, index)
  val hasDefiniteSize = true
  val size: Size = range.size

  def indexTree(index: Index): IndexTree = AtomicIndex(index)
}

// == DSL helpers ==

trait EnumOps[T1] { self: Enum[T1] =>
  def +(e2: Enum[T1]): Enum[T1] = Sum(this, e2)
  def *[T2](e2: Enum[T2]): Enum[(T1, T2)] = Product(this, e2)
  def map[U](f: T1 => U): Enum[U] = Map(this, f)
  // def filter(f: T1 => Boolean): Enum[T1] = Filter(this, f)
  def bind[U](ed: Depend[T1, U]): Enum[U] = Bind(this, ed)
  def flatMapFinite[U](f: T1 => Enum[U]): Enum[U] = Bind(this, dsl.lift(true)(f))
}

// class DependOps[V, T1](ed1: Depend[V, T1]) {
//   def +(ed2: Depend[V, T1]): Depend[V, T1] = DSum(ed1, ed2)
//   def *[T2](ed2: Depend[V, T2]): Depend[V, (T1, T2)] = DProduct(ed1, ed2)
//   def map[U](f: U => V): Depend[U, T1] = DMap(ed1, f)
// }

object dsl {
  def lift[V, T](allInnerFinite: Boolean)(f: V => Enum[T]): Depend[V, T] =
    DLift(allInnerFinite, f)
  def rec[V, T](allInnerFinite: Boolean)(f: (V, Depend[V, T]) => Enum[T]): Depend[V, T] =
    DRec(allInnerFinite, f)

  implicit def enumFromSingleton[T](value: T): Enum[T] = SingletonAtomicEnum(value)
  implicit def enumFromRange(range: Range): Enum[Int] = RangeAtomicEnum(range)
}
