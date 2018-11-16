package at.forsyte.apalache.tla.bmcmt.types

abstract class SmtExpr {
  override def toString : String = this match {
    case True => "true"
    case False => "false"
    case StrConst(name) => name
    case And() => "true"
    case And(expr) => expr.toString
    case And(exprs@_*) => s"(and ${exprs map {_.toString} mkString " " })"
    case Or() => "false"
    case Or(expr) => expr.toString
    case Or(exprs@_*) => s"(or ${exprs map {_.toString} mkString " " })"
    case Not(expr) => s"(not ${expr.toString})"
    case Eql(a, b) => s"(= ${a.toString} ${b.toString})"
    case Geql(a, b) => s"(>= ${a.toString} ${b.toString})"
    case Impl(a, b) => s"(=> ${a.toString} ${b.toString})"
    case ArgList(args@_*) => s"(${args map {_.toString} mkString " "})"
    case Forall(bVars, body) => s"(forall (${bVars map {_.toString} mkString " "}) ${body.toString})"
    case Exists(bVars, body) => s"(exists (${bVars map {_.toString} mkString " "}) ${body.toString})"
    case _ => ""
  }
}

object True extends SmtExpr
object False extends SmtExpr
sealed case class StrConst( name: String) extends SmtExpr
sealed case class And( exprs: SmtExpr* ) extends SmtExpr
sealed case class Or( exprs: SmtExpr* ) extends SmtExpr
sealed case class Not( expr: SmtExpr ) extends SmtExpr
sealed case class Eql( a: SmtExpr, b: SmtExpr ) extends SmtExpr
sealed case class Geql( a: SmtExpr, b: SmtExpr ) extends SmtExpr
sealed case class Impl( a: SmtExpr, b: SmtExpr ) extends SmtExpr
sealed case class ArgList( args: SmtExpr*) extends SmtExpr
sealed case class Forall( boundVars: List[ArgList], body: SmtExpr ) extends SmtExpr
sealed case class Exists( boundVars: List[ArgList], body: SmtExpr ) extends SmtExpr