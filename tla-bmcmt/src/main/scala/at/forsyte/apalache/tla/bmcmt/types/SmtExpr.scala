package at.forsyte.apalache.tla.bmcmt.types

import at.forsyte.apalache.tla.lir.UTFPrinter

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
    case Geq(a, b) => s"(>= ${a.toString} ${b.toString})"
    case Impl(a, b) => s"(=> ${a.toString} ${b.toString})"
    case ArgList(args@_*) => s"(${args map {_.toString} mkString " "})"
    case Forall(bVars, body) => s"(forall (${bVars map {_.toString} mkString " "}) ${body.toString})"
    case Exists(bVars, body) => s"(exists (${bVars map {_.toString} mkString " "}) ${body.toString})"
    case _ => ""
  }
  def prettyPrint : String = toString
}

object True extends SmtExpr {
  override def prettyPrint : String = s"T"
}
object False extends SmtExpr {
  override def prettyPrint : String = "\u22A5"
}
sealed case class StrConst( name: String) extends SmtExpr {
  override def prettyPrint : String = name
}
sealed case class And( exprs: SmtExpr* ) extends SmtExpr {
  override def prettyPrint : String = exprs map {_.prettyPrint} mkString s" ${UTFPrinter.m_and} "
}
sealed case class Or( exprs: SmtExpr* ) extends SmtExpr {
  override def prettyPrint : String = exprs map {_.prettyPrint} mkString s" ${UTFPrinter.m_or} "
}
sealed case class Not( expr: SmtExpr ) extends SmtExpr {
  override def prettyPrint : String = s"${UTFPrinter.m_not}[${expr.prettyPrint}]"
}
sealed case class Eql( a: SmtExpr, b: SmtExpr ) extends SmtExpr {
  override def prettyPrint : String = s"${a.prettyPrint} = ${b.prettyPrint}"
}
sealed case class Geq( a: SmtExpr, b: SmtExpr ) extends SmtExpr {
  override def prettyPrint : String = s"${a.prettyPrint} ${UTFPrinter.m_ge} ${b.prettyPrint}"
}
sealed case class Impl( a: SmtExpr, b: SmtExpr ) extends SmtExpr {
  override def prettyPrint : String = s"${a.prettyPrint} ${UTFPrinter.m_impl} ${b.prettyPrint}"
}
sealed case class ArgList( args: SmtExpr*) extends SmtExpr {
  override def prettyPrint : String = args match {
    case Seq(h) => h.prettyPrint
    case _ => s"${args.head.prettyPrint}(${args.tail map {_.prettyPrint} mkString ", " })"
  }
}
sealed case class Forall( boundVars: List[ArgList], body: SmtExpr ) extends SmtExpr {
  override def prettyPrint : String = s"${UTFPrinter.m_forall} ${boundVars map {
    case ArgList(a, b) => s"${a.prettyPrint} ${UTFPrinter.m_in} ${b.prettyPrint}"
  } mkString ", "} . ${body.prettyPrint}"
}
sealed case class Exists( boundVars: List[ArgList], body: SmtExpr ) extends SmtExpr {
  override def prettyPrint : String = s"${UTFPrinter.m_exists} ${
    boundVars map {
      case ArgList( a, b ) => s"${a.prettyPrint} ${UTFPrinter.m_in} ${b.prettyPrint}"
    } mkString ", "
  } . ${body.prettyPrint}"
}