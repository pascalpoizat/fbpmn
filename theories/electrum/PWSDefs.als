module PWSDefs

open PWSSyntax

fun inc[n : Int] : Int { plus[n,1] }
fun dec[n : Int] : Int { minus[n,1] }

// incoming edges for this node
fun Node.incoming : Edge { this.~target }

// outgoing edges from this node
fun Node.outgoing : Edge { this.~source }

// successor nodes of this node
fun Node.succs : Node { this.outgoing.target }

// predecessor nodes of this node
fun Node.preds : Node { this.incoming.source }

// incoming edges of the specified type(s)
fun Node.intype(type: set Edge) : Edge { this.incoming & type }

// outgoing edges of the specified type(s)
fun Node.outtype(type: set Edge) : Edge { this.outgoing & type }

// process or subprocess node of this node
// (immediate container)
fun Node.containInv : Container {
    this.~contains
}

