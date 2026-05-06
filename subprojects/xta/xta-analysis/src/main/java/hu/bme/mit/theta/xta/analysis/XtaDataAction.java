package hu.bme.mit.theta.xta.analysis;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xta.Guard;
import hu.bme.mit.theta.xta.Update;
import hu.bme.mit.theta.xta.XtaProcess.Edge;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.analysis.XtaAction.*;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.Streams.zip;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

public final class XtaDataAction extends StmtAction {

    private final XtaAction xtaAction;
    private volatile List<Stmt> stmts = null;

    private XtaDataAction(final XtaAction xtaAction) {
        this.xtaAction = checkNotNull(xtaAction);
    }

    public static XtaDataAction of(final XtaAction xtaAction) {
        return new XtaDataAction(xtaAction);
    }

    @Override
    public List<Stmt> getStmts() {
        List<Stmt> result = stmts;
        if (result == null) {
            if (xtaAction.isBasic()) {
                stmts = basic(xtaAction.asBasic());
            } else if (xtaAction.isBinary()) {
                stmts = binary(xtaAction.asBinary());
            } else if (xtaAction.isBroadcast()) {
                stmts = broadcast(xtaAction.asBroadcast());
            } else {
                throw new AssertionError();
            }
            result = stmts;
        }
        return result;
    }

    private List<Stmt> basic(final BasicXtaAction xtaAction) {
        final ImmutableList.Builder<Stmt> builder = ImmutableList.builder();
        final Edge edge = xtaAction.getEdge();
        addInvariants(builder, xtaAction.getSourceLocs());
        addGuards(builder, edge);
        addUpdates(builder, edge);
        addInvariants(builder, xtaAction.getTargetLocs());
        return builder.build();
    }

    private List<Stmt> binary(final BinaryXtaAction xtaAction) {
        final ImmutableList.Builder<Stmt> builder = ImmutableList.builder();
        final Edge emitEdge = xtaAction.getEmitEdge();
        final Edge recvEdge = xtaAction.getRecvEdge();
        addInvariants(builder, xtaAction.getSourceLocs());
        addSync(builder, emitEdge, recvEdge);
        addGuards(builder, emitEdge);
        addGuards(builder, recvEdge);
        addUpdates(builder, emitEdge);
        addUpdates(builder, recvEdge);
        addInvariants(builder, xtaAction.getTargetLocs());
        return builder.build();
    }

    private List<Stmt> broadcast(final BroadcastXtaAction xtaAction) {
        final ImmutableList.Builder<Stmt> builder = ImmutableList.builder();
        final Edge emitEdge = xtaAction.getEmitEdge();
        final List<Edge> recvEdges = xtaAction.getRecvEdges();
        addInvariants(builder, xtaAction.getSourceLocs());
        recvEdges.stream().forEachOrdered(recvEdge -> addSync(builder, emitEdge, recvEdge));
        addGuards(builder, emitEdge);
        recvEdges.stream().forEachOrdered(recvEdge -> addGuards(builder, recvEdge));
        addUpdates(builder, emitEdge);
        recvEdges.stream().forEachOrdered(recvEdge -> addUpdates(builder, recvEdge));
        final List<Collection<Edge>> nonRecvEdges = xtaAction.getNonRecvEdges();
        nonRecvEdges.stream().forEachOrdered(c -> c.stream().forEachOrdered(nonRecvEdge ->
                addDisabledNonRecvEdges(builder, emitEdge, nonRecvEdge)));
        addInvariants(builder, xtaAction.getTargetLocs());
        return builder.build();
    }

    private void addGuards(final ImmutableList.Builder<Stmt> builder, final Edge edge) {
        edge.getGuards().stream().filter(Guard::isDataGuard).forEach(guard -> builder.add(Assume(guard.toExpr())));
    }

    private void addUpdates(final ImmutableList.Builder<Stmt> builder, final Edge edge) {
        edge.getUpdates().stream().filter(Update::isDataUpdate).forEach(update -> builder.add(update.toStmt()));
    }

    private void addInvariants(final ImmutableList.Builder<Stmt> builder, final Collection<Loc> locs) {
        locs.forEach(loc -> loc.getInvars().stream().filter(Guard::isDataGuard).forEach(invar -> builder.add(Assume(invar.toExpr()))));
    }

    private void addSync(final ImmutableList.Builder<Stmt> builder, final Edge emitEdge, final Edge recvEdge) {
        final Stream<Expr<?>> emitArgs = emitEdge.getSync().get().getArgs().stream();
        final Stream<Expr<?>> recvArgs = recvEdge.getSync().get().getArgs().stream();
        zip(emitArgs, recvArgs, (e, r) -> Assume(Eq(e, r))).forEach(builder::add);
    }

    private void addDisabledNonRecvEdges(final ImmutableList.Builder<Stmt> builder, final Edge emitEdge, final Edge nonRecvEdge) {
        final Stream<Expr<?>> emitArgs = emitEdge.getSync().get().getArgs().stream();
        final Stream<Expr<?>> nonRecvArgs = nonRecvEdge.getSync().get().getArgs().stream();
        final Collection<Expr<BoolType>> syncAndGuardsToDisableEdge = new ArrayList<>();
        zip(emitArgs, nonRecvArgs, (e, r) -> Not(Eq(e, r)))
                .forEach(syncAndGuardsToDisableEdge::add);
        nonRecvEdge.getGuards().stream().filter(Guard::isDataGuard).map(guard -> Not(guard.toExpr()))
                .forEach(syncAndGuardsToDisableEdge::add);
        builder.add(Assume(Or(syncAndGuardsToDisableEdge)));
    }
}
