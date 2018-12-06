package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.InternalCheckerError
import at.forsyte.apalache.tla.bmcmt.types.CounterStates.CounterState
import at.forsyte.apalache.tla.bmcmt.types.NamesAndTypedefs._

import scala.collection.immutable.SortedMap
import scalaz.State._
import scalaz.Scalaz._

object StatelessFunctions {

  implicit def strToSmtConst(s: String) : StrConst = StrConst(s)

  def varNameMod( name: String ) : String = s"${varPrefix}${name}"

  def primeVarNameMod( name: String ) : String = s"${name}${primeVarSuffix}"

  def argsInParens(strs: String*) : String = s"(${strs mkString " "})"

  def setOf( s: SmtExpr ) : SmtExpr = ArgList( setTypeName, s )
  def seqOf( s: SmtExpr) : SmtExpr = ArgList( seqTypeName, s )
  def funOf( s1: SmtExpr, s2: SmtExpr) : SmtExpr = ArgList( funTypeName, s1, s2 )

  /** Makes a NameMap from a list of variable names.
    * Primes are not included, since they are structurally different in
    * the internal representation */
  def globalVarMap( variables: List[String] ) : NameMap = (variables map { v => (v, varNameMod(v) ) }).toMap

  /**
    * Used to build the toplevel Delta expression.
    * @param exBoundVars Existentially bound variables produced by a record or tuple in some subformula
    * @param typeExpr In Delta(x,_,_), we generate an expression of the form (= x `typeExpr`)
    * @param conditions Side conditions in addition to the type equation, e.g. hasIndex predicates
    */
  private sealed case class ScopedFormula( exBoundVars: List[String], typeExpr: SmtExpr, conditions: List[SmtExpr] )

  /**
    * Given an smt variable name `p_x`, a type `p_t` and a maping from type parameters to smt variables `p_m`,
    * Delta(p_x,p_t,p_m) produces the smt formula describing the fact that `p_x` is the smt representation of `p_t`,
    * together with the generated side-constraints that come from record and tuple types, such as size predicates and
    * hasField/hasIndex properties.
    */
  def delta( p_x: StrConst, p_t: SmtType, p_m : TypeMap ) : CounterState[ SmtExpr ] = {
    /**
      * We use the fact that E x. ( p(x) /\ E y . q(x,y) ) is implied by E x,y . p(x) /\ q(x,y), so we gather
      * all E-quantifed variables from subexpression and quantify them as a prefix. This simplifies the handling of hte
      * exact bound variable scopes and subformula composition significantly.
      */

    /**
      * This method generates a ScopedFormula instance, which holds the three parts of the delta formula.
      * The process is recursive in the abstract type.
      */
    def toScoped( tp : SmtType  ) : CounterState[ScopedFormula] = tp match {
      /** If the type is a type variable, there are no bound variables or side conditions generated.
        * The smt formula is simply the map-lookup value of the type parameter.
        * */
      case a : alphaT => ScopedFormula( List.empty, p_m( a ), List.empty ).point[CounterState]

      /** If the type is one of the ground types the formula is simply the smt representation of that type */
      case `intT` | `boolT` | `strT` => ScopedFormula( List.empty, StrConst( tp.name ), List.empty ).point[CounterState]

      /** For sets, we first compute the scoped formula for the contained type.
        * The formula for the set type preserves quantifiers and side constraints, but the type formula
        * is a set type wrapping the child type formula.
        * */
      case setT( tp2 ) =>
        toScoped( tp2 ) map { chd =>
          chd.copy( typeExpr = ArgList( tp.name, chd.typeExpr ) )
        }
      /** Similar to sets */
      case seqT( tp2 ) =>
        toScoped(tp2) map { chd =>
          chd.copy( typeExpr = ArgList( tp.name, chd.typeExpr ) )
        }
      /** For functions, we separately evaluate both children.
        * The bound variables and side conditions are the union of the variables/conditions of the two
        * children, the only thing that is added is the funciton constructor for the type formula
        * */
      case funT( dom, res) => for {
        chdD <- toScoped(dom)
        chdR <- toScoped(res)
      } yield ScopedFormula(
          chdD.exBoundVars ++ chdR.exBoundVars,
          ArgList( tp.name, chdD.typeExpr, chdR.typeExpr ),
          chdD.conditions ++ chdR.conditions
        )
        /** Same for operators */
      case operT( dom, res) => for {
        chdD <- toScoped( dom )
        chdR <- toScoped( res )
      } yield ScopedFormula(
          chdD.exBoundVars ++ chdR.exBoundVars,
          ArgList( tp.name, chdD.typeExpr, chdR.typeExpr ),
          chdD.conditions ++ chdR.conditions
        )

      /** For tuples, we have to add both quantified variables and side conditions, since the smt tuple type
        * abstraction loses a lot of information.
        * */
      case tupT( ts ) => for {
        /** We first create a new bound variable.  */
        boundVar <- CounterStates.inc() map { i => s"i_$i" }
        chds <- ts traverseS toScoped
      } yield {
        val newBound = boundVar +: (chds map {
          _.exBoundVars
        }).foldLeft(List.empty[String]) {
          _ ++: _
        }
        val idxConditions = chds.zipWithIndex map {
          case (sf, i) => ArgList( tupIdxFunName, boundVar, i.toString, sf.typeExpr )
        }
        val newCond =
          Eql( ArgList( tupSizeFunName, boundVar ), ts.size.toString ) +:
            idxConditions ++:
            ( chds map {
              _.conditions
            }).foldLeft( List.empty[SmtExpr] ){
              _ ++ _
            }
        ScopedFormula( newBound, ArgList( tp.name, boundVar ), newCond )
      }

      case sparseTupT( fields ) => for {
          /** We first create a new bound variable.  */
          boundVar <- CounterStates.inc() map { i => s"i_$i" }
          chds <- fields.toList traverseS { case (k, v) =>
            toScoped( v ) map { sf =>
              k -> sf
            }
          } map { lst => SortedMap( lst : _* ) }
        } yield {
          val newBound = boundVar +: ( chds.values map {
            _.exBoundVars
          } reduce {
            _ ++ _
          } )
          val idxConditions = chds map {
            case (j, sf) => ArgList( tupIdxFunName, boundVar, j.toString, sf.typeExpr )
          }
          val newCond =
            idxConditions.toList ++:
              ( chds.values.toList map {
                _.conditions
              } reduce {
                _ ++ _
              } )
          ScopedFormula( newBound, ArgList( tp.name, boundVar ), newCond )
        }

      case recT( fields ) =>
        for {
          /** We first create a new bound variable.  */
          boundVar <- CounterStates.inc() map { i => s"i_$i" }
          chds <- fields.toList traverseS { case (k, v) =>
            toScoped( v ) map { sf =>
              k -> sf
            }
          } map { lst => SortedMap( lst : _* ) }
        } yield {
          val newBound = boundVar +: ( chds.values map {
            _.exBoundVars
          } reduce {
            _ ++ _
          } )
          val fieldConditions = chds map {
            case (s, sf) => ArgList( recFieldFunName, boundVar, "\"" + s + "\"", sf.typeExpr )
          }
          val newCond =
            fieldConditions.toList ++:
              ( chds.values.toList map {
                _.conditions
              } reduce {
                _ ++ _
              } )
          ScopedFormula( newBound, ArgList( tp.name, boundVar ), newCond )
        }
    }

    toScoped(p_t) map {
      case ScopedFormula( bound, tf, cond ) =>
        val body = And( Eql( p_x, tf) +: cond :_*)

        if (bound.isEmpty)
          body
        else
          Exists( bound map {n => ArgList(n, z3Int)}, body )
    }
  }
}
