package hu.bme.mit.theta.analysis.algorithm.ic3;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.EmptyWitness;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.function.BiFunction;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class ReverseIc3Checker<S extends ExprState, A extends ExprAction> implements SafetyChecker<EmptyWitness, Trace<S, A>, UnitPrec> {
    private final MonolithicExpr monolithicExpr;
    private final SolverFactory solverFactory;

    private final Function<Valuation, S> valToState;
    private final BiFunction<Valuation, Valuation, A> biValToAction;

    public ReverseIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction) {
        this.monolithicExpr = monolithicExpr;
        this.solverFactory=solverFactory;
        this.valToState = valToState;
        this.biValToAction = biValToAction;
    }

    @Override
    public SafetyResult<EmptyWitness, Trace<S, A>> check(UnitPrec prec) {
        ExprReverser exprReverser = new ExprReverser();
        MonolithicExpr reverseMonolithicExpr = new MonolithicExpr(Not(monolithicExpr.getPropExpr()), exprReverser.reverse(monolithicExpr.getTransExpr()), Not(monolithicExpr.getInitExpr()), monolithicExpr.getTransOffsetIndex());
        Ic3Checker<S, A> ic3Checker = new Ic3Checker<S, A>(reverseMonolithicExpr,this.solverFactory, valToState, biValToAction);
        return ic3Checker.check(prec);
    }
}
