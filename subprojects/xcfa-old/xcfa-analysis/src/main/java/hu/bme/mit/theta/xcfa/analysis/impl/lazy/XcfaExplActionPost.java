package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.algorithm.lazy.expl.ExplActionPost;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;

public class XcfaExplActionPost implements ExplActionPost<XcfaAction> {
    private XcfaExplActionPost() {}

    public static XcfaExplActionPost create() {
        return new XcfaExplActionPost();
    }

    @Override
    public ExplState post(ExplState state, final XcfaAction action) {
        for(final Stmt stmt : action.getStmts()) {
            state = post(state, stmt);
        }
        return state;
    }

    private ExplState post(final ExplState state, final Stmt stmt) {
        return stmt.accept(new StmtVisitor<>() {
            @Override
            public ExplState visit(SkipStmt stmt, ExplState param) {
                return param;
            }

            @Override
            public ExplState visit(AssumeStmt stmt, ExplState param) {
                final Expr<BoolType> expr = ExprUtils.simplify(stmt.getCond(), param);
                return (expr instanceof FalseExpr) ? ExplState.bottom() : param;
            }

            @Override
            public <DeclType extends Type> ExplState visit(AssignStmt<DeclType> stmt, ExplState param) {
                final VarDecl<?> varDecl = stmt.getVarDecl();
                final Expr<?> expr = ExprUtils.simplify(stmt.getExpr(), param);
                final MutableValuation val = MutableValuation.copyOf(param);
                if (expr instanceof final LitExpr<?> value) {
                    val.put(varDecl, value);
                } else {
                    val.remove(varDecl);
                }
                return ExplState.of(val);
            }

            @Override
            public ExplState visit(SequenceStmt stmt, ExplState param) {
                for(final Stmt stmt2 : stmt.getStmts()) {
                    param = post(param, stmt2);
                }
                return param;
            }

            @Override
            public <DeclType extends Type> ExplState visit(HavocStmt<DeclType> stmt, ExplState param) {
                throw new UnsupportedOperationException();
            }

            @Override
            public ExplState visit(NonDetStmt stmt, ExplState param) {
                throw new UnsupportedOperationException();
            }

            @Override
            public ExplState visit(OrtStmt stmt, ExplState param) {
                throw new UnsupportedOperationException();
            }

            @Override
            public ExplState visit(LoopStmt stmt, ExplState param) {
                throw new UnsupportedOperationException();
            }

            @Override
            public ExplState visit(IfStmt stmt, ExplState param) {
                throw new UnsupportedOperationException();
            }
        }, state);
    }
}
