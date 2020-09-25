package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

public class XcfaStmtExecutionVisitor
        implements  StmtVisitor<Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph>, Void>,
                    XcfaStmtVisitor<Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph>, Void>{
    @Override
    public Void visit(SkipStmt stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        /* Intentionally left empty. */
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        /* Intentionally left empty. */
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        param.get1().put(param.get3().getPartitionId(param.get2()), stmt.getVarDecl(), stmt.getExpr().eval(param.get1()));
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        param.get1().remove(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(XcfaStmt xcfaStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        return xcfaStmt.accept(this, param);
    }

    @Override
    public Void visit(SequenceStmt stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(NonDetStmt stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(OrtStmt stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(XcfaCallStmt stmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(StoreStmt storeStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        param.get3().addWrite(param.get2(), storeStmt.getLhs(), storeStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(LoadStmt loadStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        param.get3().addRead(param.get2(), loadStmt.getLhs(), loadStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(FenceStmt fenceStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(AtomicBeginStmt atomicBeginStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        param.get3().setCurrentlyAtomic(param.get2());
        return null;
    }

    @Override
    public Void visit(AtomicEndStmt atomicEndStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        param.get3().setCurrentlyAtomic(null);
        return null;
    }

    @Override
    public Void visit(NotifyAllStmt notifyAllStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(NotifyStmt notifyStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(WaitStmt waitStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(MtxLockStmt lockStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(MtxUnlockStmt unlockStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(ExitWaitStmt exitWaitStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(EnterWaitStmt enterWaitStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Void visit(XcfaInternalNotifyStmt enterWaitStmt, Tuple3<MutablePartitionedValuation, XCFA.Process, ExecutionGraph> param) {
        throw new UnsupportedOperationException("Not supported yet.");
    }
}
