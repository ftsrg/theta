package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolType

/**
 * Factory class to instantiate different statements.
 *
 * @see Stmt
 */
object Stmts {

    /** Create a skip statement */
    @JvmStatic
    fun Skip(): SkipStmt = SkipStmt

    /** Create an assume statement */
    @JvmStatic
    fun Assume(cond: Expr<BoolType>): AssumeStmt = AssumeStmt(cond)

    /** Create an assignment statement */
    @JvmStatic
    fun <T : Type> Assign(
        lhs: VarDecl<T>,
        rhs: Expr<T>
    ): AssignStmt<T> = AssignStmt.of(lhs, rhs)

    /** Create a memory assignment statement */
    fun <P : Type, O : Type, T : Type> MemoryAssign(
        deref: Dereference<P, O, T>,
        expr: Expr<T>
    ): MemoryAssignStmt<P, O, T> = MemoryAssignStmt.of(deref, expr)

    /** Create a havoc statement */
    @JvmStatic
    fun <T : Type> Havoc(varDecl: VarDecl<T>): HavocStmt<T> = HavocStmt.of(varDecl)

    /** Create a sequence statement */
    @JvmStatic
    fun Sequence(stmts: List<Stmt>): SequenceStmt = SequenceStmt.of(stmts)

    /** Create a non-deterministic choice statement */
    @JvmStatic
    fun NonDet(stmts: List<Stmt>): NonDetStmt = NonDetStmt.of(stmts)
}
