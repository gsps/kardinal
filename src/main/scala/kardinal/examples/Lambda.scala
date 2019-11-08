package kardinal.examples

import kardinal.core._
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

  def subst(from: TyVarIndex, to: Type, tpe: Type): Type =
    tpe match {
      case TyVar(`from`)           => to
      case tpe @ TyVar(_)          => tpe
      case tpe @ Arrow(tpe1, tpe2) => tpe.copy(subst(from, to, tpe1), subst(from, to, tpe2))
    }

  def subst(from: TyVarIndex, to: Type, env: Env): Env =
    env match {
      case Nil => env
      case tpe :: envRest =>
        val tpeSubst = subst(from, to, tpe)
        val envRestSubst = subst(from, to, envRest)
        if ((tpeSubst ne tpe) || (envRestSubst ne envRest)) tpeSubst :: envRestSubst else env
    }

  def occurs(tv: TyVarIndex, tpe: Type): Boolean =
    tpe match {
      case TyVar(`tv`)       => true
      case Arrow(tpe1, tpe2) => occurs(tv, tpe1) || occurs(tv, tpe2)
      case _                 => false
    }

  // TODO: Speed-up occurs check by caching?
  def unify(env: Env, tpe1: Type, tpe2: Type): (Env, Type) =
    (tpe1, tpe2) match {
      case (TyVar(tv1), TyVar(tv2)) if tv1 == tv2 =>
        (env, tpe2)
      case (TyVar(tv1), tpe2) =>
        if (occurs(tv1, tpe2)) throw UnificationException else (subst(tv1, tpe2, env), tpe2)
      case (tpe1, TyVar(tv2)) =>
        if (occurs(tv2, tpe1)) throw UnificationException else (subst(tv2, tpe1, env), tpe1)
      case (Arrow(tpe1S, tpe1T), tpe2 @ Arrow(tpe2S, tpe2T)) =>
        val (newEnv1, tpeS) = unify(env, tpe1S, tpe2S)
        val (newEnv2, tpeT) = unify(newEnv1, tpe1T, tpe2T)
        (newEnv2, tpe2.copy(tpeS, tpeT))
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

  def infer(env: Env, nextTv: TyVarIndex, t: Term, expected: Type): InferResult =
    debug(s"\n${debugPre}Infer $env  |-($nextTv)  $t  :  $expected")
    {
      t match {
        case Var(v) =>
          val (newEnv, tpe) = unify(env, env(v), expected)
          (newEnv, nextTv, TypedVar(v), tpe)
        case Abs(t) =>
          val (innerEnv, innerNextTv, tt, innerTpe) = expected match {
            case Arrow(tpe1, tpe2) =>
              infer(tpe1 :: env, nextTv, t, tpe2)
            case TyVar(_) =>
              val tpeS = TyVar(nextTv)
              val tpeT = TyVar(nextTv + 1)
              val (newEnv, Arrow(newTpeS, newTpeT)) = unify(env, Arrow(tpeS, tpeT), expected)
              assert((tpeS eq newTpeS) && (tpeT eq newTpeT))
              infer(newTpeS :: newEnv, nextTv + 2, t, newTpeT)
          }
          (innerEnv.tail, innerNextTv, TypedAbs(innerEnv.head, tt), Arrow(innerEnv.head, innerTpe))
        case App(t1, t2) =>
          val tpeS = TyVar(nextTv)

          // val (newEnv1, nextTv1, tt2, newTpeS) = infer(env, nextTv + 1, t2, tpeS)
          // val (newEnv2, nextTv2, tt1, Arrow(_, tpe)) =
          //   infer(newEnv1, nextTv1, t1, Arrow(newTpeS, expected))  // FIXME: expected not unified with changes in first infer!
          // (newEnv2, nextTv2, TypedApp(tt1, tt2), tpe)

          // val (newEnv1, nextTv1, tt1, Arrow(newTpeS1, tpeT)) =
          //   infer(env, nextTv + 1, t1, Arrow(tpeS, expected))
          // val (newEnv2, nextTv2, tt2, newTpeS2) = infer(newEnv1, nextTv1, t2, newTpeS1)
          // (newEnv2, nextTv2, TypedApp(tt1, tt2), tpe)

          // ???
          val (newEnv1, nextTv1, tt2, newTpeS) = infer(env, nextTv + 1, t2, tpeS)
          val (newEnv2, nextTv2, tt1, Arrow(_, tpe)) =
            infer(newEnv1, nextTv1, t1, Arrow(newTpeS, expected))  // FIXME: expected not unified with changes in first infer!
          (newEnv2, nextTv2, TypedApp(tt1, tt2), tpe)
      }
    }

  def maybeInfer(t: Term): Option[(TypedTerm, Type)] =
    scala.util.Try(infer(Nil, 1, t, TyVar(0))).toOption.map { case (_, _, tt, tpe) => (tt, tpe) }

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
      val badTerm = closed_lambda_terms(4)(31)
      val (env, nextTv, tt, tpe) = infer(Nil, 1, badTerm, TyVar(0))
      println(s"BADTERM: ${badTerm.show}\n\t$env\n\t$nextTv\n\t$tt\n\t${tpe.show()}")
    }
  }


  // import org.scalameter.api._
  // import org.scalameter.picklers.Implicits._

  // object Benchmark extends Bench[Double] {
  //   implicit val order = Ordering.Double.IeeeOrdering
  //   lazy val executor = LocalExecutor(
  //     new Executor.Warmer.Default,
  //     Aggregator.min[Double],
  //     measurer)
  //   lazy val measurer = new Measurer.Default
  //   lazy val reporter = Reporter.Composite(
  //     new RegressionReporter(
  //       RegressionReporter.Tester.Accepter(),
  //       RegressionReporter.Historian.ExponentialBackoff()),
  //     HtmlReporter(true)
  //   )
  //   lazy val persistor = new GZIPJSONSerializationPersistor("target/results")

  //   val sizes18 = Gen.range("size")(1, 34, 1)
  //   val sizes15 = Gen.range("size")(1, 15, 1)
  //   val gen = upto(exact_unsorted)(_, _)

  //   performance of "Unsorted bit-strings up to N" in {
  //     measure method "count" config (
  //       exec.minWarmupRuns -> 100,
  //       exec.maxWarmupRuns -> 100,
  //       exec.benchRuns -> 50
  //     ) in {
  //       def run = using(sizes18) in { s => gen(s, 0 until 2).size }
  //       measure method "naive" in run
  //     }

  //     // measure method "enumerate" in {
  //     //   using(sizes15) in { s => gen(s, 0 until 2).iterator.foreach(_ => ()) }
  //     // }
  //   }
  // }
}
