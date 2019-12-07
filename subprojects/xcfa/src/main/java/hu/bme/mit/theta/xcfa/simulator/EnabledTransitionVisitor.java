package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyAllStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.WaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;

public class EnabledTransitionVisitor implements XcfaStmtVisitor<RuntimeState, Boolean> {

    @Override
    public Boolean visit(SkipStmt stmt, RuntimeState param) {
        return true;
    }

    @Override
    public Boolean visit(AssumeStmt stmt, RuntimeState state) {
        Expr<BoolType> unfolded = PathUtils.unfold(stmt.getCond(), state.vars);
        FillValuation.getInstance().fill(unfolded, state.valuation);
        BoolLitExpr a = (BoolLitExpr) unfolded.eval(state.valuation);
        return a.getValue();
    }

    @Override
    public <DeclType extends Type> Boolean visit(AssignStmt<DeclType> stmt, RuntimeState param) {
        return true;
    }

    @Override
    public <DeclType extends Type> Boolean visit(HavocStmt<DeclType> stmt, RuntimeState param) {
        return true;
    }

    @Override
    public Boolean visit(XcfaStmt xcfaStmt, RuntimeState param) {
        // TODO is this safe? return xcfaStmt.accept(this, param);
        return xcfaStmt.accept((XcfaStmtVisitor<RuntimeState, Boolean>)this, param);
    }

    @Override
    public Boolean visit(XcfaCallStmt stmt, RuntimeState param) {
        return true;
    }

    @Override
    public Boolean visit(StoreStmt storeStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(LoadStmt loadStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(AtomicBeginStmt atomicBeginStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(AtomicEndStmt atomicEndStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(NotifyAllStmt notifyAllStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(NotifyStmt notifyStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Boolean visit(WaitStmt waitStmt, RuntimeState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    private EnabledTransitionVisitor() {}

    private static EnabledTransitionVisitor instance;
    public static EnabledTransitionVisitor getInstance() {
        if (instance == null) instance = new EnabledTransitionVisitor();
        return instance;
    }

}
