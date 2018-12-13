package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.InternalCheckerError
import at.forsyte.apalache.tla.bmcmt.types.NamesAndTypedefs._
import at.forsyte.apalache.tla.lir.oper.OperArity

sealed case class SmtTemplate( arity: OperArity, private val fn: templateType ) {

  def apply( x: String, ts: List[String] ) : SpecState[SmtExpr] =
    if ( arity.cond( ts.size ) )
      fn(x,ts)
    else
      throw new InternalCheckerError( s"Incorrect template arity. Expected ${arity}, got ${ts.size}." )
}

sealed case class SmtInternal(
                               partialSpec: String,
                               nextVar: Int,
                               nextBound: Int,
                               knownTemplates: Map[String, SmtTemplate],
                               labelMap: LabelMap
                             ) {
  def +(that: String) : SmtInternal = this.copy( partialSpec = partialSpec + that )
  def inc : SmtInternal = this.copy( nextVar = nextVar + 1)
  def incB : SmtInternal = this.copy( nextBound = nextBound + 1)
}

object SmtInternal {
  def init(variables: List[String] = List.empty) : SmtInternal =
    SmtInternal(partialSpec = "", nextVar = 0, nextBound = 0, knownTemplates = Map.empty, labelMap = Map.empty)
}
