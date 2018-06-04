package at.forsyte.apalache.tla.types.tsa

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, UID, ValEx}
import at.forsyte.apalache.tla.types.{TypeError, TypeException, TypeWarn, tsa}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * A type inference engine for Type System A.
  *
  * @param typeMap the storage for the inferred types
  *
  * @author Igor Konnov
  */
class TypeInferer(val typeMap: mutable.Map[UID, CellT]) {
  /**
    * The counter used to introduce fresh unknowns.
    */
  private var maxVarCounter = 0

  /**
    * The list of errors accumulated during type inference.
    */
  private var foundErrors: ListBuffer[TypeError] = ListBuffer()

  /**
    * The list of warnings accumulated during type inference.
    */
  private var foundWarnings: ListBuffer[TypeWarn] = ListBuffer()

  /**
    * Get the list of collected errors.
    * @return the list of collected errors
    */
  def errors: List[TypeError] = foundErrors.toList

  /**
    * Get the list of collected warnings.
    * @return the list of collected warnings
    */
  def warnings: List[TypeWarn] = foundWarnings.toList

  /**
    * Recursively infer the types of all subexpressions and store them.
    *
    * @param e a TLA+ expression
    * @return the inferred type
    * @throws TypeException if the expression cannot be assigned a sound type.
    */
  def inferRecAndStore(e: TlaEx): CellT = {
    def store(inferredType: CellT) = {
      typeMap.put(e.ID, inferredType)
      inferredType
    }
    e match {
        case ValEx(TlaInt(_)) =>
          store(IntT())     // -1, 0, 3, 100

        case ValEx(TlaBool(_)) =>
          store(BoolT())    // FALSE, TRUE

        case ValEx(TlaStr(_)) =>
          store(ConstT())   // "abc"

        case OperEx(oper: TlaOper, lhs, rhs)
            if TypeInferer.equalities.contains(oper.name) =>
          // equalities: =, /=
          inferRecAndStore(lhs); inferRecAndStore(rhs) // infer the types of arguments
          expectNonComparableArgs(e, lhs, rhs)
          store(BoolT())

        case OperEx(_: TlaBoolOper, _*) =>
          // Boolean operators: and, or, not, equiv, implies, \E, \A
          store(inferBoolean(e))

        case OperEx(oper: TlaArithOper, args @ _*) =>
          // arithmetics: +, -, *, /, mod, <, <=, >, >=, prod, sum, a^b, a..b
          store(inferArithType(e, oper, args))

        case OperEx(oper, args @ _*)
            if TypeInferer.uniformSetOps.contains(oper.name) =>
          // set operators: \cup, \cap, \setminus, {...}
          store(FinSetT(inferUniformType(e, oper, args)))

        case OperEx(TlaSetOper.union, args @ _*) =>
          // UNION ...
          store(inferUnion(e, args))

        case OperEx(TlaSetOper.filter, _, setEx, predEx) =>
          // { x \in S: p(x) }
          store(inferSetFilter(e, setEx, predEx))

        case OperEx(oper: TlaFiniteSetOper, set) =>
          // IsFiniteSet({...}) and Cardinality({...})
          store(inferFiniteSetOper(e, oper, set))

        case _ =>
          store(UnknownT(TypeInferer.mkVarName(nextCounter())))
      }
  }

  private def inferBoolean(ex: TlaEx): CellT = {
    ex match {
      case OperEx(oper: TlaBoolOper, args@_*)
        if TypeInferer.boolOps.contains(oper.name) =>
        // Boolean operators: and, or, not, equiv, implies
        args foreach inferRecAndStore
        args foreach expectBoolean

      case OperEx(oper: TlaBoolOper, name, set, pred)
        if TypeInferer.boundedQuantifiers.contains(oper.name) =>
        // \E x \in S: p and \A x \in S: p
        inferRecAndStore(set)
        expectFiniteSet(set)
        inferRecAndStore(pred)
        expectBoolean(pred)

      case OperEx(oper: TlaBoolOper, name, pred)
        if TypeInferer.unboundedQuantifiers.contains(oper.name) =>
        // \E x: p and \A x: p
        inferRecAndStore(pred)
        expectBoolean(pred)

      case _ =>
        throw new TypeException("Unexpected TlaBoolOper")
    }

    BoolT()
  }

  private def inferArithType(ex: TlaEx, oper: TlaArithOper, args: Seq[TlaEx]): CellT = {
    // FIXME: for the moment, only integers are supported
    args foreach inferRecAndStore
    args foreach expectInt
    if (TypeInferer.arithNonComparisons.contains(oper.name)) {
      IntT()
    } else if (TypeInferer.arithComparisons.contains(oper.name)) {
      // when the arguments are non-uniform, inferUniformType records an error
      BoolT()
    } else if (oper.name == TlaArithOper.dotdot.name) {
      FinSetT(IntT())
    } else {
      UnknownT(TypeInferer.mkVarName(nextCounter()))
    }
  }

  private def inferUniformType(ex: TlaEx, oper: TlaOper, args: Seq[TlaEx]): CellT = {
    val argTypes = args map inferRecAndStore
    val unifier =
      if (argTypes.nonEmpty)
        tsa.unify(argTypes: _*)
      else Some(UnknownT(TypeInferer.mkVarName(nextCounter())))
    unifier match {
      case Some(tp) => tp

      case None =>
        val typesStr = String.join(", ", argTypes.map(_.toString) :_*)
        val msg = "Failed to unify types %s".format(typesStr)
        foundErrors += TypeError(ex.ID, msg)
        UnknownT(TypeInferer.mkVarName(nextCounter()))
    }
  }

  private def inferUnion(ex: TlaEx, args: Seq[TlaEx]): CellT = {
    inferUniformType(ex, TlaSetOper.union, args) match {
      case FinSetT(et) => et
      case tp =>
        // TODO: add an error to foundErrors
        throw new TypeException("Expected FinSets as UNION arguments")
    }
  }

  private def inferSetFilter(ex: TlaEx, setEx: TlaEx, predEx: TlaEx): CellT = {
    inferRecAndStore(predEx)
    expectBoolean(predEx)
    inferRecAndStore(setEx) match {
      case setType @ FinSetT(et) => setType
      case tp =>
        foundErrors += TypeError(ex.ID, "Set comprehension applied to type " + tp)
        UnknownT(TypeInferer.mkVarName(nextCounter()))
    }
  }

  private def expectNonComparableArgs(ex: TlaEx, lhs: TlaEx, rhs: TlaEx): Unit = {
    val (lt, rt) = (typeMap(lhs.ID), typeMap(rhs.ID))
    if (lt != rt) {
      val msg = "Constant comparison result, as types %s and %s differ".format(lt, rt)
      foundWarnings += TypeWarn(ex.ID, msg)
    }
  }

  private def expectBoolean(ex: TlaEx): Unit = {
    val tp = typeMap(ex.ID)
    if (tp != BoolT()) {
      val msg = "Expected a Boolean, found " + tp
      foundErrors += TypeError(ex.ID, msg)
    }
  }

  private def expectInt(ex: TlaEx): Unit = {
    val tp = typeMap(ex.ID)
    if (tp != IntT()) {
      val msg = "Expected an integer, found " + tp
      foundErrors += TypeError(ex.ID, msg)
    }
  }

  private def expectFiniteSet(ex: TlaEx): Unit = {
    typeMap(ex.ID) match {
      case FinSetT(_) | FinFunSetT(_, _) | PowSetT(_) =>
        () // OK

      case tp =>
        val msg = "Expected a set, found " + tp
        foundErrors += TypeError(ex.ID, msg)
    }
  }

  private def inferFiniteSetOper(ex: TlaEx, oper: TlaFiniteSetOper, set: TlaEx): CellT = {
    inferRecAndStore(set)
    expectFiniteSet(set)
    if (oper.name == TlaFiniteSetOper.isFiniteSet.name) {
      BoolT()
    } else if (oper.name == TlaFiniteSetOper.cardinality.name) {
      IntT()
    } else {
      UnknownT(TypeInferer.mkVarName(nextCounter()))
    }
  }

  private def nextCounter(): Int = {
    val counter = maxVarCounter
    maxVarCounter += 1
    counter
  }
}


object TypeInferer {
  /**
    * Operators that treat their arguments uniformly.
    */
  private val uniformSetOps =
    Set(TlaSetOper.enumSet.name, TlaSetOper.cap.name, TlaSetOper.cup.name, TlaSetOper.setminus.name)

  /**
    * Arithmetic operators except comparisons.
    */
  private val arithNonComparisons =
    Set(TlaArithOper.plus.name, TlaArithOper.minus.name, TlaArithOper.mult.name,
      TlaArithOper.div.name, TlaArithOper.mod.name, TlaArithOper.uminus.name,
      TlaArithOper.sum.name, TlaArithOper.prod.name, TlaArithOper.exp.name)

  /**
    * Arithmetic comparisons.
    */
  private val arithComparisons =
    Set(TlaArithOper.lt.name, TlaArithOper.le.name,
      TlaArithOper.gt.name, TlaArithOper.ge.name)

  /**
    * Equality and inequality.
    */
  private val equalities =
    Set(TlaOper.eq.name, TlaOper.ne.name)

  /**
    * Boolean operators.
    */
  private val boolOps =
    Set(TlaBoolOper.and.name, TlaBoolOper.or.name, TlaBoolOper.not.name,
        TlaBoolOper.equiv.name, TlaBoolOper.implies.name)

  /**
    * Bounded quantifiers.
    */
  private val boundedQuantifiers = Set(TlaBoolOper.exists.name, TlaBoolOper.forall.name)

  /**
    * Unbounded quantifiers.
    */
  private val unboundedQuantifiers =
    Set(TlaBoolOper.existsUnbounded.name, TlaBoolOper.forallUnbounded.name)

  /**
    * Letters used in type variables.
    */
  private val letters =
    List("a", "b", "c", "d", "e", "f", "g", "h", "i", "j",
      "k", "l", "m", "n", "o", "p", "q", "r", "s", "t",
      "u", "v", "w", "x", "y", "z")
  private val lettersCnt = letters.length

  /**
    * Map an non-negative integer to a human-readable string, e.g., a, bc, efg.
    * @param i an non-negative integer
    * @return the name associated with i
    */
  def mkVarName(i: Int): String = {
    if (i < lettersCnt)
      letters(i)
    else
      letters(i % lettersCnt) + mkVarName(i / lettersCnt)
  }
}
