package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.bmcmt.types.NamesAndTypedefs._

import scalaz.State
import scalaz.Scalaz._

sealed case class SmtInternal(
                               partialSpec: String,
                               nextVar: Int,
                               globalVarMap : NameMap,
                               knownTemplates: Map[String, templateType]
                             ) {
  def +(that: String) : SmtInternal = this.copy( partialSpec = partialSpec + that )
  def inc : SmtInternal = this.copy( nextVar = nextVar + 1)
}

object SmtInternal {
  def init(variables: List[String] = List.empty) : SmtInternal =
    SmtInternal(partialSpec = "", nextVar = 0, globalVarMap = StatelessFunctions.globalVarMap(variables), knownTemplates = Map.empty)
}
