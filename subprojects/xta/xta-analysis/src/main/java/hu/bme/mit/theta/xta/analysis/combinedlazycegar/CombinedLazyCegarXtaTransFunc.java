package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.xta.Guard;
import hu.bme.mit.theta.xta.Selection;
import hu.bme.mit.theta.xta.Update;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BasicXtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BinaryXtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BroadcastXtaAction;

import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;

@SuppressWarnings("UnstableApiUsage")
public class CombinedLazyCegarXtaTransFunc<S extends State, P extends Prec> implements TransFunc<S, XtaAction, P> {

    private final TransFunc<S, ? super ExprAction, P> transFunc;

    private CombinedLazyCegarXtaTransFunc(final TransFunc<S, ? super ExprAction, P> transFunc) {
        this.transFunc = checkNotNull(transFunc);
    }

    public static <S extends State, P extends Prec> CombinedLazyCegarXtaTransFunc<S, P> create(final TransFunc<S, ? super ExprAction, P> transFunc) {
        return new CombinedLazyCegarXtaTransFunc<>(transFunc);
    }

    @Override
    public Collection<? extends S> getSuccStates(final S state, final XtaAction action, final P prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);

        if (action.isBasic()) {
            return getSuccStatesForBasicAction(state, action.asBasic(), prec);
        } else if (action.isBinary()) {
            return getSuccStatesForBinaryAction(state, action.asBinary(), prec);
        } else if (action.isBroadcast()) {
            return getSuccStatesForBroadcastAction(state, action.asBroadcast(), prec);
        } else {
            throw new AssertionError();
        }
    }

    private Collection<? extends S> getSuccStatesForBasicAction(final S state, final BasicXtaAction action, final P prec) {
        return applyStmtsToState(
            state,
            Streams.concat(
                selectionsToStmt(action.getEdge().getSelections()),
                guardsToStmt(action.getEdge().getGuards()),
                dataUpdatesToStmt(action.getEdge().getUpdates()),
                dataInvariantsToStmt(action.getTargetLocs())
            ).toList(),
            prec
        );
    }

    private Collection<? extends S> getSuccStatesForBinaryAction(final S state, final BinaryXtaAction action, final P prec) {
        return applyStmtsToState(
            state,
            Streams.concat(
                syncToStmt(action.getEmitEdge(), action.getRecvEdge()),
                selectionsToStmt(action.getEmitEdge().getSelections()),
                selectionsToStmt(action.getRecvEdge().getSelections()),
                guardsToStmt(action.getEmitEdge().getGuards()),
                guardsToStmt(action.getRecvEdge().getGuards()),
                dataUpdatesToStmt(action.getEmitEdge().getUpdates()),
                dataUpdatesToStmt(action.getEmitEdge().getUpdates()),
                dataUpdatesToStmt(action.getRecvEdge().getUpdates()),
                dataInvariantsToStmt(action.getTargetLocs())
            ).toList(),
            prec
        );
    }

    private Collection<? extends S> getSuccStatesForBroadcastAction(final S state, final BroadcastXtaAction action, final P prec) {
        return applyStmtsToState(
            state,
            Streams.concat(
                action.getRecvEdges().stream()
                    .flatMap(recvEdge -> syncToStmt(action.getEmitEdge(), recvEdge)),
                selectionsToStmt(action.getEmitEdge().getSelections()),
                action.getRecvEdges().stream()
                    .flatMap(recvEdge -> selectionsToStmt(recvEdge.getSelections())),
                guardsToStmt(action.getEmitEdge().getGuards()),
                action.getRecvEdges().stream()
                    .flatMap(recvEdge -> guardsToStmt(recvEdge.getGuards())),
                dataUpdatesToStmt(action.getEmitEdge().getUpdates()),
                action.getRecvEdges().stream()
                    .flatMap(recvEdge -> dataUpdatesToStmt(recvEdge.getUpdates())),
                action.getNonRecvEdges().stream()
                    .flatMap(Collection::stream)
                    .flatMap(nonRecvEdge -> nonRecvSyncAndGuardsToStmt(action.getEmitEdge(), nonRecvEdge)),
                dataInvariantsToStmt(action.getTargetLocs())
            ).toList(),
            prec
        );
    }

    private Collection<? extends S> applyStmtsToState(final S state, final List<Stmt> stmts, final P prec) {
        return transFunc.getSuccStates(state, new BasicStmtAction(stmts), prec);
    }

    private static Stream<? extends Stmt> selectionsToStmt(final Collection<Selection> selections) {
        return selections.stream()
            .map(Selection::toStmt);
    }

    private static Stream<? extends Stmt> guardsToStmt(final Collection<Guard> guards) {
        return guards.stream()
            .filter(Guard::isDataGuard)
            .map(Guard::asDataGuard)
            .map(g -> Assume(g.toExpr()));
    }

    private static Stream<? extends Stmt> dataUpdatesToStmt(final Collection<Update> updates) {
        return updates.stream()
            .filter(Update::isDataUpdate)
            .map(Update::asDataUpdate)
            .map(Update.DataUpdate::toStmt);
    }

    private static Stream<? extends Stmt> dataInvariantsToStmt(final List<XtaProcess.Loc> locs) {
        return locs.stream()
            .map(XtaProcess.Loc::getInvars)
            .flatMap(CombinedLazyCegarXtaTransFunc::guardsToStmt);
    }

    private static Stream<? extends Stmt> syncToStmt(final XtaProcess.Edge emitEdge, final XtaProcess.Edge recvEdge) {
        checkArgument(emitEdge.getSync().isPresent());
        checkArgument(recvEdge.getSync().isPresent());

        return Streams.zip(
            emitEdge.getSync().get().getArgs().stream(),
            recvEdge.getSync().get().getArgs().stream(),
            (e, r) -> Assume(AbstractExprs.Eq(e, r))
        );
    }

    private static Stream<? extends Stmt> nonRecvSyncAndGuardsToStmt(final XtaProcess.Edge emitEdge, final XtaProcess.Edge nonRecvEdge) {
        checkArgument(emitEdge.getSync().isPresent());
        checkArgument(nonRecvEdge.getSync().isPresent());

        final var nonRecvArgs = Streams.zip(
            emitEdge.getSync().get().getArgs().stream(),
            nonRecvEdge.getSync().get().getArgs().stream(),
            (e, r) -> BoolExprs.Not(AbstractExprs.Eq(e, r))
        );
        final var notGuards = nonRecvEdge.getGuards().stream()
            .filter(Guard::isDataGuard)
            .map(Guard::asDataGuard)
            .map(Guard.DataGuard::toExpr)
            .map(SmartBoolExprs::Not);

        return Stream.of(Assume(BoolExprs.Or(Streams.concat(nonRecvArgs, notGuards).toList())));
    }

    private final static class BasicStmtAction extends StmtAction {
        private final List<Stmt> stmts;

        private BasicStmtAction(final List<Stmt> stmts) {
            this.stmts = stmts;
        }

        @Override
        public List<Stmt> getStmts() {
            return stmts;
        }
    }

}
