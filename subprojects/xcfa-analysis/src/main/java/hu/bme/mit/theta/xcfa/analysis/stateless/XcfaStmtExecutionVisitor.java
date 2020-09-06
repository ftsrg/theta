package hu.bme.mit.theta.xcfa.analysis.stateless;

import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.graph.ExecutionGraph;

public class XcfaStmtExecutionVisitor
        implements  StmtVisitor<Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph>, Void>,
                    XcfaStmtVisitor<Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph>, Void>{
    @Override
    public Void visit(SkipStmt stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        /* Intentionally left empty. */
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        /* Intentionally left empty. */
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        param.get1().put(stmt.getVarDecl(), stmt.getExpr().eval(param.get1()));
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        param.get1().remove(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(XcfaStmt xcfaStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        return xcfaStmt.accept(this, param);
    }

    @Override
    public Void visit(SequenceStmt stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(NonDetStmt stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(OrtStmt stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(XcfaCallStmt stmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(StoreStmt storeStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        param.get4().addRead(storeStmt.getLhs(), storeStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(LoadStmt loadStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        param.get4().addRead(loadStmt.getRhs(), loadStmt.getLhs());
        return null;
    }

    @Override
    public Void visit(AtomicBeginStmt atomicBeginStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        param.get2().setCurrentlyAtomic(param.get3());
        return null;
    }

    @Override
    public Void visit(AtomicEndStmt atomicEndStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        param.get2().setCurrentlyAtomic(null);
        return null;
    }

    @Override
    public Void visit(NotifyAllStmt notifyAllStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(NotifyStmt notifyStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(WaitStmt waitStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(MtxLockStmt lockStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(MtxUnlockStmt unlockStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(ExitWaitStmt exitWaitStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(EnterWaitStmt enterWaitStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(XcfaInternalNotifyStmt enterWaitStmt, Tuple4<MutableValuation, State, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }
}
