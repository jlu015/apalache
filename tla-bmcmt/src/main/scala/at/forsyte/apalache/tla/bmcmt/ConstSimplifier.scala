package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * A simplifier of constant TLA+ expressions, e.g., rewriting 1 + 2 to 3.
  *
  * @author Igor Konnov
  */
class ConstSimplifier {
  def simplify(rootExpr: TlaEx): TlaEx = {
    def rewriteDeep(ex: TlaEx): TlaEx = ex match {
      case NameEx(_) | ValEx(_) =>
        ex

      case OperEx(oper, args @ _*) =>
        simplifyShallow(OperEx(oper, args map rewriteDeep :_*))

      case _ =>
        ex
    }

    rewriteDeep(rootExpr)
  }

  def simplifyShallow(ex: TlaEx): TlaEx = ex match {
    case NameEx(_) | ValEx(_) => ex

    // integer operations
    case OperEx(TlaArithOper.plus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left + right))

    case OperEx(TlaArithOper.minus, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left - right))

    case OperEx(TlaArithOper.mult, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left * right))

    case OperEx(TlaArithOper.div, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left / right))

    case OperEx(TlaArithOper.mod, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaInt(left % right))

    case OperEx(TlaArithOper.exp, ValEx(TlaInt(base)), ValEx(TlaInt(power))) =>
      ValEx(TlaInt(Math.pow(base.toDouble, power.toDouble).toInt))

    case OperEx(TlaArithOper.uminus, ValEx(TlaInt(value))) =>
      ValEx(TlaInt(-value))

    case OperEx(TlaArithOper.lt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left < right))

    case OperEx(TlaArithOper.le, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left <= right))

    case OperEx(TlaArithOper.gt, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left > right))

    case OperEx(TlaArithOper.ge, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left >= right))

    case OperEx(TlaOper.eq, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left == right))

    case OperEx(TlaOper.ne, ValEx(TlaInt(left)), ValEx(TlaInt(right))) =>
      ValEx(TlaBool(left != right))

    // boolean operations
    case OperEx(TlaBoolOper.and, args @ _*) if args.contains(ValEx(TlaBool(false))) =>
      ValEx(TlaBool(false))

    case OperEx(TlaBoolOper.and, args @ _*) if args.forall (_.isInstanceOf[ValEx]) =>
      val result = !args.contains(ValEx(TlaBool(false)))
      ValEx(TlaBool(result))

    case OperEx(TlaBoolOper.or, args @ _*) if args.contains(ValEx(TlaBool(true))) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.or, args @ _*) if args.forall (_.isInstanceOf[ValEx]) =>
      val result = args.contains(ValEx(TlaBool(true)))
      ValEx(TlaBool(result))

    case OperEx(TlaBoolOper.not, ValEx(TlaBool(b))) =>
      ValEx(TlaBool(!b))

    case OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, underDoubleNegation)) =>
      underDoubleNegation

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(!left || right))

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(false)), _) =>
      ValEx(TlaBool(true))

    case OperEx(TlaBoolOper.implies, ValEx(TlaBool(true)), right) =>
      OperEx(TlaBoolOper.not, right)

    case OperEx(TlaBoolOper.equiv, ValEx(TlaBool(left)), ValEx(TlaBool(right))) =>
      ValEx(TlaBool(left == right))

    case OperEx(TlaBoolOper.equiv, ValEx(TlaBool(left)), right) =>
      if (left) {
        right
      } else {
        OperEx(TlaBoolOper.not, right)
      }

    case OperEx(TlaBoolOper.equiv, left, ValEx(TlaBool(right))) =>
      if (right) {
        left
      } else {
        OperEx(TlaBoolOper.not, left)
      }

    // default
    case _ =>
      ex
  }

}
