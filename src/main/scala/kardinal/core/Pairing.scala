package kardinal.core

import scala.math.{floor, sqrt}
import scala.collection.mutable.ArrayBuffer

// == Pairings ==

trait Pairing {
  def decompose(index: Index): (Index, Index)
}

object SumPairing {
  // 2nd component = index into 1st-component-th enum
  def apply[T](e1: Enum[T], e2: Enum[T]): Pairing = {
    Linear2(e1.size)
  }
}

object ProductPairing {
  // 1st component = index into 1st enum
  // 2nd component = index into 2nd enum
  def apply[T1, T2](e1: Enum[T1], e2: Enum[T2]): Pairing = {
    DivMod2(e1.size)
  }
}


case class Linear2(size1: Size) extends Pairing {
  def decompose(index: Index) =
    if (index < size1) (0, index) else (1, index - size1)
}

case class LinearK(innerSizes: Iterator[Size]) extends Pairing {
  private var lastSum: Index = 0
  private val prefixSums: ArrayBuffer[Size] = ArrayBuffer(0)

  def decompose(index: Index): (Index, Index) = {
    // Ensure chunks covering items up to `index` have been aggregated
    while (lastSum <= index) {
      if (innerSizes.hasNext) {
        lastSum += innerSizes.next()
        prefixSums.append(lastSum)
      } else {
        // `index` is out-of-bounds anyways, generate out-of-bounds first component
        return (prefixSums.length - 1, 0)
      }
    }
    // Find our chunk
    // TODO: For large enough `lastSum`, do binary search instead
    var i: Int = 1
    while (prefixSums(i) <= index) {
      i += 1
    }
    i -= 1
    (i, index - prefixSums(i))
  }
}

case class DivMod2(size1: Size) extends Pairing {
  def decompose(index: Index) =
    (index % size1, index / size1)
}

object Cantor2 extends Pairing {
  ???
  def decompose(index: Index) = {
    val i = index
    val w = floor((sqrt(8 * i.toDouble + 1) - 1) / 2).toInt
    (index - (w*w + w) / 2, (w*w + 3*w) / 2 + index)
  }
}

object Szudzik2 extends Pairing {
  ???
  def decompose(index: Index) = {
    val i = index
    val ir = floor(sqrt(index)).toInt
    val w = i - ir*ir
    if (w < ir)
      (w, ir)
    else
      (ir, w - ir)
  }
}