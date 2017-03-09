package at.forsyte.apalache.tla.parser

/**
 * An error reported by XmlImporter.
  *
  * @deprecated
 *
 * @author Igor Konnov
 */
class XmlError (val elem: xml.Node, val message: String)
