package hu.bme.mit.theta.core.stmt

import kotlinx.serialization.Polymorphic

/**
 * Base class for all statements in the Theta framework.
 * All subclasses must be serializable.
 */
@Polymorphic
interface Stmt {
    /**
     * Accepts a visitor and returns the result of the visit.
     * @param visitor The visitor to accept
     * @param param Additional parameter for the visitor
     * @return The result of the visit
     */
    fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R
}
