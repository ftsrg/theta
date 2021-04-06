package hu.bme.mit.theta.xcfa.ir.handlers.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.Argument;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.RegArgument;

import java.util.Map;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class PlaceholderAssignmentStmt<T extends Type> implements Stmt {
    private final VarDecl<T> lhs;
    private final Argument rhsKey;

    public static <T extends Type> PlaceholderAssignmentStmt<T> of(VarDecl<T> lhs, Argument rhsKey) {
        return new PlaceholderAssignmentStmt<T>(lhs, rhsKey);
    }
    private PlaceholderAssignmentStmt(VarDecl<T> lhs, Argument rhsKey) {
        this.lhs = lhs;
        this.rhsKey = rhsKey;
    }

    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        throw new RuntimeException("PlaceholderStmt should not be treated as a normal statement.");
    }

    public Argument getRhsKey() {
        return rhsKey;
    }

    public VarDecl<T> getLhs() {
        return lhs;
    }

    public AssignStmt<T> toAssignStmt(Map<String, Expr<?>> values) {
        return Assign(lhs, cast(rhsKey.getExpr(values), lhs.getType()));
    }
}
