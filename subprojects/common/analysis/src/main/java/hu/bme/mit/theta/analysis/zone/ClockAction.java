package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.clock.op.ClockOp;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public final class ClockAction extends StmtAction {

    private final Collection<ClockOp> ops;

    private ClockAction(Collection<ClockOp> ops) {
        this.ops = ops;
    }

    public static ClockAction create(Collection<ClockOp> ops){
        return new ClockAction(ops);
    }

    public Collection<ClockOp> getClockOps(){
        return ops;
    }

    @Override
    public List<Stmt> getStmts() {
        final List<Stmt> stmts = new ArrayList<>(ops.size());
        ops.forEach(op -> stmts.add(op.toStmt()));
        return stmts;
    }

}
