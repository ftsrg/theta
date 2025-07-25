package hu.bme.mit.theta.xta;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rangetype.InRangeExpr;
import hu.bme.mit.theta.core.type.rangetype.RangeType;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public final class Selection {

    private final VarDecl<RangeType> varDecl;

    private Selection(VarDecl<RangeType> varDecl) {
        this.varDecl = varDecl;
    }

    public static Selection create(VarDecl<RangeType> varDecl) {
        return new Selection(varDecl);
    }

    public final VarDecl<RangeType> getVarDecl() {
        return varDecl;
    }

    public final Stmt toStmt() {
        final Expr<IntType> varRef = TypeUtils.cast(varDecl.getRef(), Int());
        final RangeType range = varDecl.getType();
        final InRangeExpr inRange = InRangeExpr.of(varRef, range);
        return SequenceStmt.of(List.of(Havoc(varDecl), Assume(inRange)));
    }

    @Override
    public String toString() {
        return String.format("select %s", varDecl);
    }
}
