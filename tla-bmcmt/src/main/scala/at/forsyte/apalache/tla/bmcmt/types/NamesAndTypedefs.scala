package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.lir.{TlaOperDecl, UID}

import scalaz.State

object NamesAndTypedefs {

  type Spec = String

  type SpecState[T] = State[SmtInternal, T]

  type void = SpecState[Unit]

  type templateType = (String, List[String]) => SpecState[SmtExpr]

  type TypeMap = Map[alphaT, StrConst]
  
  type NameMap = Map[String, String]

  type DeclMap = Map[String, TlaOperDecl]

  type LabelMap = Map[String, UID]

  val typeName          : String = "T"
  val intTypeName       : String = "intT"
  val boolTypeName      : String = "boolT"
  val strTypeName       : String = "strT"
  val varTypeName       : String = "alpha"
  val varAccessorName   : String = "i"
  val setTypeName       : String = "set"
  val setAccessorName   : String = "st"
  val seqTypeName       : String = "seq"
  val seqAccessorName   : String = "sq"
  val recTypeName       : String = "rec"
  val recAccessorName   : String = "r"
  val tupTypeName       : String = "tup"
  val tupAccessorName   : String = "j"
  val funTypeName       : String = "fun"
  val argAccessorName   : String = "arg"
  val resAccessorName   : String = "res"
  val operTypeName      : String = "oper"
  val oargAccessorName  : String = "oarg"
  val oresAccessorName  : String = "ores"
  val z3Int             : String = "Int"
  val z3Str             : String = "String"
  val z3Bool            : String = "Bool"
  val emptyArg          : String = "()"
  val unknownVarFunName : String = "unknownVar"
  val labelTypeFunName  : String = "typeOfLabel"
  val recFieldFunName   : String = "hasField"
  val tupIdxFunName     : String = "hasIndex"
  val tupSizeFunName    : String = "sizeOf"
  val isVarFunName      : String = "isAlpha"
  val idTag             : String = ":id"
  val weightTag         : String = ":weight"
  val defaultIdTagName  : String = "nAlphas"
  val varPrefix         : String = "var_"
  val primeVarSuffix    : String = "_prime"


}
