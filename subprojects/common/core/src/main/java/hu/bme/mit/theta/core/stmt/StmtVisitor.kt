package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.core.type.Type

/**
 * Visitor interface for the statement hierarchy.
 * @param <P> The type of the parameter
 * @param <R> The return type of the visit operations
 */
interface StmtVisitor<in P, out R> {
    fun visit(stmt: SkipStmt, param: P): R
    fun visit(stmt: AssumeStmt, param: P): R
    fun <DeclType : Type> visit(stmt: AssignStmt<DeclType>, param: P): R
    fun <PtrType : Type, OffsetType : Type, DeclType : Type> visit(
        stmt: MemoryAssignStmt<PtrType, OffsetType, DeclType>,
        param: P
    ): R

    fun <DeclType : Type> visit(stmt: HavocStmt<DeclType>, param: P): R
    fun visit(stmt: SequenceStmt, param: P): R
    fun visit(stmt: NonDetStmt, param: P): R
    fun visit(stmt: OrtStmt, param: P): R
    fun visit(stmt: LoopStmt, param: P): R
    fun visit(stmt: IfStmt, param: P): R
}
