package at.forsyte.apalache.tla.bmcmt.types

import NamesAndTypedefs._

import scala.collection.SortedMap

abstract class SmtType {
  val name: String
}

object intT extends SmtType{
  override val name : String = intTypeName
}

object boolT extends SmtType {
  override val name : String = boolTypeName
}
object strT extends SmtType {
  override val name : String = strTypeName
}

sealed case class setT( t: SmtType ) extends SmtType {
  override val name : String = setTypeName
}
sealed case class seqT( t: SmtType ) extends SmtType {
  override val name : String = seqTypeName
}
sealed case class tupT( ts: List[SmtType] ) extends SmtType {
  override val name : String = tupTypeName
}
sealed case class funT( arg: SmtType, res: SmtType ) extends SmtType {
  override val name : String = funTypeName
}
sealed case class recT( fields: SortedMap[String,SmtType] ) extends SmtType {
  override val name : String = recTypeName
}
sealed case class alphaT( i: Int ) extends SmtType {
  override val name : String = varTypeName
}
