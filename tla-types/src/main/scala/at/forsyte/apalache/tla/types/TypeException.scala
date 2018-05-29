package at.forsyte.apalache.tla.types

/**
  * An exception related to a type error.
  *
  * @param message error message
  */
class TypeException(message: String) extends Exception(message)
