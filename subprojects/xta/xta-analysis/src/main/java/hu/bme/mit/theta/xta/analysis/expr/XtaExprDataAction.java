package hu.bme.mit.theta.xta.analysis.expr;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xta.Guard;
import hu.bme.mit.theta.xta.Update;
import hu.bme.mit.theta.xta.XtaProcess.Edge;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.*;

import java.util.ArrayList;
import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.Streams.zip;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public final class XtaExprDataAction implements ExprAction {

    private final XtaAction xtaAction;
    private volatile Expr<BoolType> expr = null;
    private volatile VarIndexing nextIndexing = null;

    private XtaExprDataAction(final XtaAction xtaAction) {
        this.xtaAction = checkNotNull(xtaAction);
    }

    public static XtaExprDataAction of(final XtaAction xtaAction) {
        return new XtaExprDataAction(xtaAction);
    }

    @Override
    public Expr<BoolType> toExpr() {
        Expr<BoolType> result = expr;
        if (result == null) {
            set();
            result = expr;
        }
        return result;
    }

    @Override
    public VarIndexing nextIndexing() {
        VarIndexing result = nextIndexing;
        if (result == null) {
            set();
            result = nextIndexing;
        }
        return result;
    }

    private void set() {
        if (xtaAction.isBasic()) {
            setBasic(xtaAction.asBasic());
        } else if (xtaAction.isBinary()) {
            setBinary(xtaAction.asBinary());
        } else if (xtaAction.isBroadcast()) {
            setBroadcast(xtaAction.asBroadcast());
        } else {
            throw new AssertionError();
        }
    }

    private void setBasic(final BasicXtaAction xtaAction) {
        final Collection<Expr<BoolType>> actionExprs = new ArrayList<>();
        final Edge edge = xtaAction.getEdge();

        addGuards(edge, actionExprs);

        final VarIndexing indexing = addUpdates(edge, actionExprs);

        addInvars(xtaAction.getTargetLocs(), indexing, actionExprs);

        expr = And(actionExprs);
        nextIndexing = indexing;
    }

    private void setBinary(final BinaryXtaAction xtaAction) {
        final Collection<Expr<BoolType>> actionExprs = new ArrayList<>();
        final Edge emitEdge = xtaAction.getEmitEdge();
        final Edge recvEdge = xtaAction.getRecvEdge();

        addSync(emitEdge, recvEdge, actionExprs);

        addGuards(emitEdge, actionExprs);
        addGuards(recvEdge, actionExprs);

        final VarIndexing indexing1 = addUpdates(emitEdge, actionExprs);
        final VarIndexing indexing2 = addUpdates(recvEdge, actionExprs);
        final VarIndexing indexing = indexing1.join(indexing2);

        addInvars(xtaAction.getTargetLocs(), indexing, actionExprs);

        expr = And(actionExprs);
        nextIndexing = indexing;
    }

    private void setBroadcast(final BroadcastXtaAction xtaAction) {
        final Collection<Expr<BoolType>> actionExprs = new ArrayList<>();
        final Edge emitEdge = xtaAction.getEmitEdge();
        final Collection<Edge> recvEdges = xtaAction.getRecvEdges();

        recvEdges.forEach(recvEdge -> addSync(emitEdge, recvEdge, actionExprs));

        addGuards(emitEdge, actionExprs);
        recvEdges.forEach(recvEdge -> addGuards(recvEdge, actionExprs));

        Collection<Collection<Edge>> nonRecvEdges = xtaAction.getNonRecvEdges();
        nonRecvEdges.forEach(
                edges -> edges.forEach(
                        nonRecvEdge -> addNonRecvEdgeNotDefinitelyEnabled(emitEdge, nonRecvEdge, actionExprs)
                )
        );

        final VarIndexing.Builder indexingBuilder = addUpdates(emitEdge, actionExprs).transform();
        recvEdges.forEach(recvEdge -> indexingBuilder.join(addUpdates(recvEdge, actionExprs).transform()));
        final VarIndexing indexing = indexingBuilder.build();

        addInvars(xtaAction.getTargetLocs(), indexing, actionExprs);

        expr = And(actionExprs);
        nextIndexing = indexing;
    }

    private void addGuards(final Edge edge, final Collection<Expr<BoolType>> actionExprs) {
        final Collection<Expr<BoolType>> dataGuardExprs = edge.getGuards().stream()
                .filter(Guard::isDataGuard)
                .map(Guard::toExpr)
                .collect(Collectors.toUnmodifiableList());
        actionExprs.addAll(dataGuardExprs);
    }

    private VarIndexing addUpdates(final Edge edge, final Collection<Expr<BoolType>> actionExprs) {
        final Collection<Update> updates = edge.getUpdates();
        final Collection<Expr<BoolType>> dataUpdateExprs = new ArrayList<>();
        VarIndexing.Builder indexingBuilder = VarIndexing.builder(0);
        for (final Update update : updates) {
            if (update.isDataUpdate()) {
                final Stmt updateStmt = update.toStmt();
                final StmtUnfoldResult toExprResult = StmtUtils.toExpr(updateStmt, VarIndexing.all(0));
                dataUpdateExprs.addAll(toExprResult.getExprs());
                indexingBuilder.join(toExprResult.getIndexing().transform());
            }
        }
        actionExprs.addAll(dataUpdateExprs);
        return indexingBuilder.build();
    }

    private void addInvars(final Collection<Loc> locs, final VarIndexing varIndexing,
                           final Collection<Expr<BoolType>> actionExprs) {
        final Collection<Expr<BoolType>> invarExprs = new ArrayList<>();
        for (final Loc loc : locs) {
            final Collection<Guard> invars = loc.getInvars();
            for (final Guard invar : invars) {
                if (invar.isDataGuard()) {
                    final Expr<BoolType> invarExpr = withPrimes(invar.toExpr(), varIndexing);
                    invarExprs.add(invarExpr);
                }
            }
        }
        actionExprs.addAll(invarExprs);
    }

    private <T extends Type> Expr<T> withPrimes(final Expr<T> expr, final VarIndexing varIndexing) {
        if (expr instanceof RefExpr) {
            final RefExpr<?> refExpr = (RefExpr<?>) expr;
            final Decl<?> decl = refExpr.getDecl();
            if (decl instanceof VarDecl) {
                final VarDecl<?> varDecl = (VarDecl<?>) decl;
                int nPrimes = varIndexing.get(varDecl);
                if (nPrimes > 0) {
                    return Exprs.Prime(expr, nPrimes);
                }
            }
        }
        return expr.map(op -> withPrimes(op, varIndexing));
    }

    private void addSync(final Edge emitEdge, final Edge recvEdge, final Collection<Expr<BoolType>> actionExprs) {
        final Stream<Expr<?>> emitArgsStream = emitEdge.getSync().get().getArgs().stream();
        final Stream<Expr<?>> recvArgsStream = recvEdge.getSync().get().getArgs().stream();
        final Collection<Expr<BoolType>> syncExprs
                = zip(emitArgsStream, recvArgsStream, AbstractExprs::Eq).collect(Collectors.toUnmodifiableList());
        actionExprs.addAll(syncExprs);
    }

    private void addNonRecvEdgeNotDefinitelyEnabled(final Edge emitEdge, final Edge nonRecvEdge,
                                                    final Collection<Expr<BoolType>> actionExprs) {
        final Collection<Expr<BoolType>> conditions = new ArrayList<>();
        addGuards(nonRecvEdge, conditions);
        addSync(emitEdge, nonRecvEdge, conditions);
        final Expr<BoolType> nonRecvEdgeDefinitelyEnabled = And(conditions);
        final Expr<BoolType> nonRecvEdgeNotDefinitelyEnabled = Not(nonRecvEdgeDefinitelyEnabled);
        actionExprs.add(nonRecvEdgeNotDefinitelyEnabled);
    }

}
