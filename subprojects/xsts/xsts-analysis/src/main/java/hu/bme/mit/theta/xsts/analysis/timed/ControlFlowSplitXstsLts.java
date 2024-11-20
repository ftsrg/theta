package hu.bme.mit.theta.xsts.analysis.timed;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.stmtoptimizer.StmtSimplifier;
import hu.bme.mit.theta.analysis.utils.ValuationExtractor;
import hu.bme.mit.theta.core.clock.impl.RatClockImpl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;

import java.util.*;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.clocktype.ClockExprs.Clock;

public class ControlFlowSplitXstsLts<S extends ExprState> implements LTS<XstsState<S>, XstsAction> {

    private final Solver solver;
    private final ValuationExtractor<S> valExtractor;

    private final NonDetStmt init;
    private final NonDetStmt tran;
    private final NonDetStmt env;
    private final Set<VarDecl<?>> ctrlVars;

    private final Function<Stmt, Stmt> stmtClockTransformer;
    private final Map<Stmt, ControlFlowSplitResult> cfSplitCache;

    private ControlFlowSplitResult cfSplitResult;
    private ExprState lastState;

    private ControlFlowSplitXstsLts(final XSTS xsts, final Solver solver, final ValuationExtractor<S> valExtractor) {
        this.solver = solver;
        this.valExtractor = valExtractor;

        init = xsts.getInit();
        tran = xsts.getTran();
        env = xsts.getEnv();
        ctrlVars = xsts.getCtrlVars();

        final List<VarDecl<ClockType>> clocks = xsts.getVars().stream()
                .filter(varDecl -> varDecl.getType() instanceof ClockType)
                .map(varDecl -> TypeUtils.cast(varDecl, Clock()))
                .toList();
        if (clocks.isEmpty()) {
            stmtClockTransformer = stmt -> stmt;
        } else {
            stmtClockTransformer = RatClockImpl.fromClocks(clocks)::transformStmt;
        }
        cfSplitCache = new HashMap<>();
    }

    public static <S extends ExprState> ControlFlowSplitXstsLts<S> create(final XSTS xsts, final Solver solver,
                                                                          final ValuationExtractor<S> valExtractor) {
        return new ControlFlowSplitXstsLts<>(xsts, solver, valExtractor);
    }

    @Override
    public Collection<XstsAction> getEnabledActionsFor(XstsState<S> state) {
        reset();
        splitControlFlows(state, false);
        final List<XstsAction> actions = new ArrayList<>();
        Optional<XstsAction> action = getNextEnabledAction();
        while (action.isPresent()) {
            actions.add(action.get());
            action = getNextEnabledAction();
        }
        return actions;
    }

    public void reset() {
        if (!solver.getAssertions().isEmpty()) {
            solver.pop();
        }
        lastState = null;
    }

    public void splitControlFlows(final XstsState<S> state, final boolean feasibleOnly) {
        final Stmt enabledSet;
        if (!state.isInitialized()) enabledSet = init;
        else if (state.lastActionWasEnv()) enabledSet = tran;
        else enabledSet = env;

        final Valuation ctrlVal = valExtractor.extractValuationForVars(state.getState(), ctrlVars);
        final Stmt simplifiedStmt = StmtSimplifier.simplifyStmt(ctrlVal, enabledSet);
        cfSplitResult = cfSplitCache.computeIfAbsent(simplifiedStmt, ControlFlowSplitUtil::splitControlFlows);

        solver.push();
        solver.add(cfSplitResult.getIndexedFlagConstraintExpr());
        if (feasibleOnly) {
            final Stmt stmtWithoutClocks = stmtClockTransformer.apply(cfSplitResult.getFlaggedStmt());
            StmtUtils.toExpr(stmtWithoutClocks, VarIndexingFactory.indexing(0)).getExprs()
                    .forEach(expr -> solver.add(PathUtils.unfold(expr, 0)));
        }
    }

    public void updateSourceAbstractState(final ExprState state) {
        if (state != lastState) {
            solver.add(PathUtils.unfold(state.toExpr(), 0));
        }
    }

    public Optional<XstsAction> getNextEnabledAction() {
        if (solver.getAssertions().isEmpty()) {
            throw new IllegalStateException();
        }

        final SolverStatus status = solver.check();
        if (status.isSat()) {
            final Valuation model = solver.getModel();
            final Collection<VarDecl<BoolType>> flags = cfSplitResult.getFlags();
            final Valuation flagsVal = PathUtils.extractValuation(model, 0, flags);

            final List<Expr<BoolType>> negatedFlags = new ArrayList<>();
            for (final VarDecl<BoolType> flag : flags) {
                final Optional<LitExpr<BoolType>> flagValue = flagsVal.eval(flag);
                if (flagValue.isPresent()) {
                    final BoolLitExpr boolValue = (BoolLitExpr) flagValue.get();
                    negatedFlags.add(boolValue.getValue() ? Not(flag.getRef()) : flag.getRef());
                }
            }
            solver.add(PathUtils.unfold(Or(negatedFlags), 0));

            final Stmt flaggedStmt = cfSplitResult.getFlaggedStmt();
            final Stmt resultStmt = StmtSimplifier.simplifyStmt(flagsVal, flaggedStmt);
            final XstsAction action = XstsAction.create(resultStmt);

            return Optional.of(action);

        } else {
            return Optional.empty();
        }
    }
}
