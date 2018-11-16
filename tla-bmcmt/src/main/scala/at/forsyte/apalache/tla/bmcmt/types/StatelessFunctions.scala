package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.InternalCheckerError
import at.forsyte.apalache.tla.bmcmt.types.NamesAndTypedefs._

object StatelessFunctions {
  implicit def strToSmtConst(s: String) : StrConst = StrConst(s)

  def varNameMod( name: String ) : String = s"${varPrefix}${name}"

  def primeVarNameMod( name: String ) : String = s"${name}${primeVarSuffix}"

  def argsInParens(strs: String*) : String = s"(${strs mkString " "})"

  def globalVarMap( variables: List[String] ) : NameMap = (variables map { v => (v, varNameMod(v) ) }).toMap

  private sealed case class ScopedFormula( exBoundVars: List[String], typeExpr: SmtExpr, conditions: List[SmtExpr] )

  def delta( p_x: StrConst, p_t: SmtType, p_m : TypeMap ) : SmtExpr = {

    def toScoped( tp : SmtType  ) : ScopedFormula = tp match {
      case a : alphaT => ScopedFormula(List.empty, p_m(a), List.empty )
      case `intT` | `boolT` | `strT` => ScopedFormula(List.empty, StrConst(tp.name), List.empty)
      case setT( tp2 ) =>
        val chd = toScoped(tp2)
        chd.copy( typeExpr = ArgList(tp.name, chd.typeExpr) )
      case seqT( tp2 ) =>
        val chd = toScoped(tp2)
        chd.copy( typeExpr = ArgList(tp.name, chd.typeExpr) )
      case funT( dom, res) =>
        val chdD = toScoped(dom)
        val chdR = toScoped(res)
        ScopedFormula(
          chdD.exBoundVars ++ chdR.exBoundVars,
          ArgList( tp.name, chdD.typeExpr, chdR.typeExpr ),
          chdD.conditions ++ chdR.conditions
        )
      case tupT( ts ) =>
        val boundVar = s"i_${tp.hashCode()}"
        val chds = ts map toScoped
        val newBound = boundVar +: (chds map {_.exBoundVars} reduce {_ ++ _})
        val idxConditions = chds.zipWithIndex map {
          case (sf,i) => ArgList( tupIdxFunName, boundVar, i.toString, sf.typeExpr )
        }
        val newCond  =
          Eql( ArgList( tupSizeFunName, boundVar ), ts.size.toString ) +:
          idxConditions ++:
          (chds map {_.conditions} reduce {_ ++ _})
        ScopedFormula( newBound, ArgList( tp.name, boundVar ), newCond )

      case recT( fields ) =>
        val boundVar = s"i_${tp.hashCode()}"
        val chds = fields map { case (k,v) => k -> toScoped(v) }
        val newBound = boundVar +: (chds.values map {_.exBoundVars} reduce {_ ++ _})
        val fieldConditions = chds map {
          case (s,sf) => ArgList( recFieldFunName, boundVar, s, sf.typeExpr )
        }
        val newCond  =
          fieldConditions.toList ++:
          (chds.values.toList map {_.conditions} reduce {_ ++ _})
        ScopedFormula( newBound, ArgList( tp.name, boundVar ), newCond )
    }

    val ScopedFormula( bound, tf, cond ) = toScoped(p_t)
    val body = And( Eql( p_x, tf) +: cond :_*)

    if (bound.isEmpty)
      body
    else
      Exists( bound map {n => ArgList(n, z3Int)}, body )

//    t match {
//    // assumption: |f| = |t.args|
//    case intT | boolT | strT => Eql( x, t.name )
//    case setT( t2 : alphaT ) => Eql( x, ArgList( t.name, m(t2) ) )
//    case seqT( t2 : alphaT ) => Eql( x, ArgList( t.name, m(t2) ) )
//    case funT( dom: alphaT, res : alphaT) =>
//      Eql( x, ArgList( (t.name +: (List(dom, res) map {m(_)})) map strToSmtConst:_* ) )
//    case tupT( ts : List[alphaT] ) =>
//      val boundVar = "i"
//      val bigwedge = ts.zipWithIndex map {
//        case (ti,i) => ArgList( tupIdxFunName, boundVar, i.toString, m(ti))
//      }
//      Exists(
//        List(ArgList(boundVar, z3Int)),
//        And(
//          Eql( x, ArgList( t.name, boundVar ) ) +:
//            Eql( ArgList( tupSizeFunName, boundVar ), ts.size.toString ) +:
//            bigwedge :_*
//        )
//      )
//    case recT( fields : Map[String,alphaT] ) =>
//      val boundVar = "i"
//      val bigwedge = fields.toList map {
//        case (s, ti) => ArgList( recFieldFunName, boundVar, s, m(ti))
//      }
//      Exists(
//        List(ArgList(boundVar, z3Int)),
//        And( Eql( x, ArgList( recTypeName, boundVar ) ) +: bigwedge :_* )
//      )
//    case _ =>
//      throw new InternalCheckerError( s"Unexpected type: ${t}}" )
//
//  }

  }

}
