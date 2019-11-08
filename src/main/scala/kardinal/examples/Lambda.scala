package kardinal.examples

import kardinal.core.{Map => _, _}
import kardinal.core.dsl._

object Lambda {

  /* == Untyped lambda terms == */

  type TermSize = Int
  type VarIndex = Int

  sealed trait Term {
    def show(): String = this match {
      case Var(v) => v.toString
      case Abs(t) => s"λ ${t.show}"
      case App(t1, t2) =>
        val left = t1 match {
          case Abs(_) => s"(${t1.show})"
          case _      => t1.show
        }
        val right = t2 match {
          case App(_, _) => s"${t2.show}"
          case _         => t2.show
        }
        s"$left $right"
    }
  }
  final case class Var(v: VarIndex) extends Term
  final case class Abs(t: Term) extends Term
  final case class App(t1: Term, t2: Term) extends Term

  // All closed lambda terms of size `s`, counting variables as 0-sized.
  def closed_lambda_terms(s: TermSize): Enum[Term] =
    rec[(TermSize, VarIndex), Term](true) {
      case ((size, maxIndex), self) =>
        if (size == 0) {
          enumFromRange(0 until maxIndex) map Var
        } else {
          val sizeRest = size - 1
          val abss: Enum[Term] = self((sizeRest, maxIndex + 1)) map Abs
          val apps: Enum[Term] = (0 to sizeRest) flatMapFinite (
              sizeLeft => self((sizeLeft, maxIndex)) * self((sizeRest - sizeLeft, maxIndex))
          ) map App.tupled
          abss + apps
        }
    }.apply((s, 0))

  /* == Simply-typed lambda terms == */

  sealed trait TypedTerm
  final case class TypedVar(i: VarIndex) extends TypedTerm
  final case class TypedAbs(tpe: Type, t: TypedTerm) extends TypedTerm
  final case class TypedApp(t1: TypedTerm, t2: TypedTerm) extends TypedTerm

  type TyVarIndex = Int
  type Env = List[Type]
  type InferResult = (Env, TyVarIndex, TypedTerm, Type)
  object UnificationException extends Exception

  val MaxNesting = 16

  sealed trait Type {
    import scala.collection.immutable.Map
    private def makeNames(): Map[TyVarIndex, String] = {
      def indices(tpe: Type): Set[TyVarIndex] = tpe match {
        case TyVar(v)          => Set(v)
        case Arrow(tpe1, tpe2) => indices(tpe1) ++ indices(tpe2)
      }
      val tvs = indices(this).toSeq.sorted
      val names =
        if (tvs.size <= 26) (0 until 26).map(o => ('A' + o).toChar.toString)
        else Iterator.from(0).map(o => s"T$o")
      tvs.zip(names).toMap
    }
    def show(names: Map[TyVarIndex, String] = Map.empty): String = {
      val _names = if (names.isEmpty) makeNames() else names
      this match {
        case TyVar(tv)                       => s"${_names(tv)}"
        case Arrow(tpe1 @ Arrow(_, _), tpe2) => s"(${tpe1.show(_names)}) →  ${tpe2.show(_names)}"
        case Arrow(tpe1, tpe2)               => s"${tpe1.show(_names)} →  ${tpe2.show(_names)}"
      }
    }
  }
  final case class TyVar(v: TyVarIndex) extends Type
  final case class Arrow(tpe1: Type, tpe2: Type) extends Type {
    def copy(tpe1: Type, tpe2: Type): Type =
      if ((this.tpe1 ne tpe1) || (this.tpe2 ne tpe2)) Arrow(tpe1, tpe2) else this
  }

  /*
  type Subst = Array[Type]
  object Subst {
    private val identityTemplate: Subst = Array.fill(MaxNesting)(null)
    def identity = identityTemplate.clone

    def singleton(from: TyVarIndex, to: Type): Subst = {
      val s = identity
      s(from) = to
      s
    }

    def apply(s: Subst, tpe: Type): Type =
      tpe match {
        case TyVar(tv) =>
          val to = s(tv)
          if (to ne null) to else tpe
        case tpe @ Arrow(tpe1, tpe2) =>
          tpe.copy(apply(s, tpe1), apply(s, tpe2))
      }

    def compose(s1: Subst, s2: Subst): Type = {
      val s: Subst = s2.clone
      for (i <- 0 until MaxNesting) {
        var tpe = s2(i)
        if (tpe eq null)
          tpe = TyVar(i)
        s(i) = subst(s1, tpe)
      }
      s
    }

    def extend(from: TyVarIndex, to: Type, s: Subst): Subst =
      compose(singleton(from, to), s)
  }
  implicit class SubstOps(subst: Subst) {
    def apply(tpe: Type): Type = Subst.apply(subst, tpe)
    def compose(other: Subst): Subst = Subst.compose(subst, other)
  }
   */

  case class Subst(pairs: Map[TyVarIndex, Type]) {
    def apply(tv: TyVarIndex): Type = pairs.getOrElse(tv, TyVar(tv))
    def apply(tpe: Type): Type =
      tpe match {
        case TyVar(tv)               => pairs.getOrElse(tv, tpe)
        case tpe @ Arrow(tpe1, tpe2) => tpe.copy(apply(tpe1), apply(tpe2))
      }
    def compose(other: Subst): Subst =
      Subst(this.pairs ++ other.pairs.view.mapValues(apply))
    def drop(tv: TyVarIndex): Subst =
      Subst(pairs - tv)
  }
  object Subst {
    val identity = Subst(Map.empty)
    def singleton(from: TyVarIndex, to: Type) = Subst(Map(from -> to))
  }

  def occurs(tv: TyVarIndex, tpe: Type): Boolean =
    tpe match {
      case TyVar(`tv`)       => true
      case Arrow(tpe1, tpe2) => occurs(tv, tpe1) || occurs(tv, tpe2)
      case _                 => false
    }

  // TODO: Speed-up occurs check by caching?
  def unifier(tpe1: Type, tpe2: Type): Subst =
    (tpe1, tpe2) match {
      case (TyVar(tv1), TyVar(tv2)) if tv1 == tv2 =>
        Subst.identity
      case (tpe1, TyVar(tv2)) =>
        if (occurs(tv2, tpe1)) throw UnificationException else Subst.singleton(tv2, tpe1)
      case (TyVar(tv1), tpe2) =>
        if (occurs(tv1, tpe2)) throw UnificationException else Subst.singleton(tv1, tpe2)
      case (Arrow(tpe1S, tpe1T), tpe2 @ Arrow(tpe2S, tpe2T)) =>
        unifier(tpe1S, tpe2S) compose unifier(tpe1T, tpe2T)
    }

  def merge(s1: Subst, s2: Subst): Subst =
    (s1.pairs.keySet union s2.pairs.keySet).foldLeft(s1) {
      case (s, tv) => unifier(s1(tv), s2(tv)) compose s
    }

  private var debugDepth: Int = 1
  private def debugPre: String = "  " * debugDepth
  private def debug(msg: String)(f: => InferResult): InferResult = {
    println(msg)
    debugDepth += 1
    val res @ (env, nextTv, _, tpe) = f
    debugDepth -= 1
    println(s"$debugPre╚════ $env  |-($nextTv)  _  :  $tpe\n")
    res
  }

  private var _nextTv: Int = MaxNesting
  private def freshTv(): TyVar = {
    val t = TyVar(_nextTv)
    _nextTv += 1
    t
  }

  // // `n` is the number of free variables, the implicit environment is one where each variable
  // // has as its type `TyVar(i)` where `i` corresponds to the relative depth of its binding.
  // Note that `env` is simple here, in the sense that each variable is of a distinct type variable
  def principal(env: Env, t: Term): (TypedTerm, Type, Subst) = {
    assert(env.reverse.zipWithIndex forall { case (TyVar(tv), i) => tv == i; case _ => false })
    assert(env.size <= MaxNesting)
    t match {
      case Var(v) =>
        (TypedVar(v), env(v), Subst.identity)
      case Abs(t) =>
        val paramTv = env.size
        val tpeS = TyVar(paramTv)
        val (tt, tpeT, ut) = principal(tpeS :: env, t)
        val tpeS_unif = ut(tpeS)
        (TypedAbs(tpeS_unif, tt), Arrow(tpeS_unif, tpeT), ut drop paramTv)
      case App(t1, t2) =>
        val (tt1, tpe1, ut1base) = principal(env, t1)
        val (tt2, tpe2, ut2base) = principal(env, t2)
        val tpeS = freshTv()
        val tpeT = freshTv()
        val ut1abs = unifier(tpe1, Arrow(tpeS, tpeT))
        val ut2arg = unifier(tpe2, tpeS)
        val ut1 = ut1base compose ut1abs
        val ut2 = ut2base compose ut2arg
        val ut = merge(ut1, ut2)
        (TypedApp(tt1, tt2), ut(tpeT), ut)
    }
  }

  def maybeInfer(t: Term): Option[(TypedTerm, Type)] =
    scala.util.Try(principal(Nil, t)).toOption.map { case (tt, tpe, ut) => (tt, tpe) }

  def computeType(env: Env, tt: TypedTerm): Option[Type] =
    tt match {
      case TypedVar(v)        => Some(env(v))
      case TypedAbs(tpeS, tt) => computeType(tpeS :: env, tt).map(Arrow(tpeS, _))
      case TypedApp(tt1, tt2) =>
        for {
          Arrow(tpeS1, tpeT) <- computeType(env, tt1)
          tpeS2 <- computeType(env, tt2)
          if tpeS1 == tpeS2
        } yield tpeT
    }

  def checkType(tt: TypedTerm, tpe: Type): Boolean =
    computeType(Nil, tt).map(_ == tpe).getOrElse(false)

  // All closed simply-typed lambda terms of size `s`, counting variables as 0-sized.
  def closed_typed_lambda_terms(s: TermSize): Enum[Term] =
    rec[(TermSize, VarIndex), Term](true) {
      case ((size, maxIndex), self) =>
        if (size == 0) {
          enumFromRange(0 until maxIndex) map Var
        } else {
          val sizeRest = size - 1
          val abss: Enum[Term] = self((sizeRest, maxIndex + 1)) map Abs
          val apps: Enum[Term] = (0 to sizeRest) flatMapFinite (
              sizeLeft => self((sizeLeft, maxIndex)) * self((sizeRest - sizeLeft, maxIndex))
          ) map App.tupled
          abss + apps
        }
    }.apply((s, 0))

  /* == Entrypoint == */

  def demo(): Unit = {
    val N: Int = 4

    val PrettyPrint: Boolean = true
    val CBad: String = Console.RED
    val CGood: String = Console.GREEN
    val CReset: String = Console.RESET

    def runOne(name: String, n: Int, gen: Int => Enum[Term]): Unit = {
      val terms = gen(n)
      val numTerms = terms.size
      // println(s" == $name ==")
      println(s"# of $name of size $n: $numTerms")
      // terms.iterator.foreach(term => println(s"  - $term"))
      var numIlltyped = 0
      terms.iterator.zipWithIndex foreach {
        case (term, index) =>
          val optTpe = maybeInfer(term) match {
            case Some((tt, tpe)) =>
              if (!checkType(tt, tpe))
                println(s"UHOH: $tt  :/  $tpe")
              Some(tpe)
            case None =>
              numIlltyped += 1
              None
          }
          if (PrettyPrint) {
            val indexStr = "%03d".format(index)
            if (optTpe.isEmpty) println(s"$CBad  $indexStr:  ${term.show}  :  XXX$CReset")
            else println(s"$CGood  $indexStr:  ${term.show}  :  ${optTpe.get.show()}$CReset")
          } else {
            println(s"  - $term  :  ${optTpe.getOrElse("XXX").toString}")
          }
      }
      println(s"  => # well-typed: ${numTerms - numIlltyped}")
      println("")
    }

    // (1 to N) foreach { n =>
    //   runOne("closed lambda terms", n, closed_lambda_terms)
    // }
    {
      val badTerm = closed_lambda_terms(2)(2)
      val (tt, tpe, ut) = principal(Nil, badTerm)
      println(s"BADTERM: ${badTerm.show}\n\t$tt\n\t${tpe.show()}\n\t${_nextTv}\n\t$ut")
    }
  }
}
