package kardinal.core

// == Index trees (decomposed indices) ==

sealed abstract trait IndexTree
case class AtomicIndex(index: Index) extends IndexTree
case class Decomposed(pairing: Pairing, left: IndexTree, right: IndexTree) extends IndexTree
