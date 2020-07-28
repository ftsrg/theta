package hu.bme.mit.theta.xcfa.alt.transform;

import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;

import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.xcfa.EnterWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.ExitWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.WaitStmt;
import hu.bme.mit.theta.xcfa.XCFA;

/**
 * Transforms empty edges to edge with skip stmt.
 * Transforms wait stmt's to two separate stmts.
 */
public class DefaultTransformation extends EmptyTransformation {

    public DefaultTransformation(XCFA old) {
        super(old);
    }

    @Override
    protected XCFA.Process.Procedure.Edge copy(Object _builder, XCFA.Process.Procedure.Edge edge) {
        if (edge.getStmts().isEmpty()) {
            // create skip stmt
            var source = transformed(_builder, edge.getSource());
            var target = transformed(_builder, edge.getTarget());
            return new XCFA.Process.Procedure.Edge(
                    source, target, List.of(SkipStmt.getInstance())
            );
        }
        Preconditions.checkArgument(edge.getStmts().size() == 1);
        if (edge.getStmts().get(0) instanceof WaitStmt) {
            var stmt = (WaitStmt) edge.getStmts().get(0);
            var source = transformed(_builder, edge.getSource());
            var target = transformed(_builder, edge.getTarget());
            var mid = new XCFA.Process.Procedure.Location(source.getName() + "_midwait",
                    Map.of());
            var e1 = new XCFA.Process.Procedure.Edge(source, mid, List.of(
                    new EnterWaitStmt(stmt.getCndSyncVar())
            ));
            var e2 = new XCFA.Process.Procedure.Edge(mid, target, List.of(
                    new ExitWaitStmt(stmt.getCndSyncVar()) // TODO add Mtx capability
            ));

            var builder = (XCFA.Process.Procedure.Builder)_builder;
            builder.addLoc(mid);
            builder.addEdge(e2);
            return e1; //builder.addEdge(e1);
        } else {
            return super.copy(_builder, edge);
        }
    }
}
