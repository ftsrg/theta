package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

/** Updates state without checking enabledness. Does not update locations. */
public class StateUpdateVisitor implements XcfaStmtVisitor<CallState, Void> {

    private StateUpdateVisitor() {
    }

    private static StateUpdateVisitor instance;

    public static StateUpdateVisitor getInstance() {
        if (instance == null) instance = new StateUpdateVisitor();
        return instance;
    }

    @Override
    public Void visit(XcfaCallStmt _stmt, CallState param) {
        Preconditions.checkArgument(_stmt instanceof CallStmt, "XcfaCallStmt should be a CallStmt!");
        CallStmt stmt = (CallStmt) _stmt;
        // paraméterek befelé: stmt.getParams()
        // az, amit hívnak: stmt.getProcedure()
        // visszatérési értéket stmt.getVar()-ba kell írni
        ProcessState process = param.parent;
        if (stmt.isVoid()) {
            process.push(stmt.getProcedure(), stmt.getParams());
        } else {
            process.push(stmt.getProcedure(), stmt.getParams(), stmt.getVar());
        }
        return null;
    }

    @Override
    public Void visit(StoreStmt storeStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(LoadStmt loadStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(AtomicBeginStmt atomicBeginStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(AtomicEndStmt atomicEndStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(NotifyAllStmt notifyAllStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(NotifyStmt notifyStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(WaitStmt waitStmt, CallState param) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Void visit(SkipStmt stmt, CallState param) {
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, CallState param) {
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, CallState param) {
        RuntimeState state = param.parent.parent;
        Expr<? extends Type> unfolded = PathUtils.unfold(stmt.getExpr(), state.vars);

        IndexedConstDecl<DeclType> y = stmt.getVarDecl().getConstDecl(state.vars.get(stmt.getVarDecl()));
        FillValuation.getInstance().fill(unfolded, state.valuation);
        LitExpr x = unfolded.eval(state.valuation);
        state.valuation.put(y, x);
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, CallState param) {
        RuntimeState state = param.parent.parent;
        state.valuation.remove(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(XcfaStmt xcfaStmt, CallState param) {
        return xcfaStmt.accept(this, param);
    }

}
