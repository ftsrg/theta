package hu.bme.mit.theta.frontend.model

import Btor2Sort

abstract class Btor2Node(open val nid: UInt, open val sort: Btor2Sort? = null) {
    abstract fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R
}
