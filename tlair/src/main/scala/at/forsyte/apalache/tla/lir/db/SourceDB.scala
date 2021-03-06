package at.forsyte.apalache.tla.lir.db

import at.forsyte.apalache.tla.lir.UID

class SourceDB extends HashMapDB[UID, UID] {
  override val m_name : String = "sourceDB"

  override def put( key : UID,
                    value : UID
                  ) : Option[UID] =
    if( key.valid && value.valid ) super.put( key, value )
    else None

  override def update( key : UID,
                       value : UID
                     ) : Unit =
    if (key.valid && value.valid) super.update( key, value )

  def traceBack( p_id : UID ) : UID = get( p_id ) match {
    case Some( id ) => traceBack( id )
    case _ => p_id
  }
}

object DummySrcDB extends SourceDB {
  override val m_name : String = "DummySourceDB"

  override def put( key : UID,
                    value : UID
                  ) : Option[UID] = None

  override def update( key : UID,
                       value : UID
                     ) : Unit = {}

  override def get( key : UID ) : Option[UID] = None

  override def size : Int = 0

  override def contains( key : UID ) : Boolean = false

  override def remove( key : UID ) : Unit = {}

  override def clear( ) : Unit = {}

  override def print( ) : Unit = {}

  override def traceBack( p_id : UID ) : UID = p_id

  override def apply( key : UID ) : UID = UID( -1 )

  override def keyCollection : Traversable[UID] = Set.empty[UID]

  /** Retrieves the value associated with the key, if it exists in the database, otherwise returns `elseVal`. */
  override def getOrElse( key : UID,
                          elseVal : UID
                        ) : UID = UID( -1 )
}
