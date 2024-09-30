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
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;

public class ConnectedIc3Checker<S extends ExprState, A extends ExprAction> implements SafetyChecker<EmptyWitness, Trace<S, A>, UnitPrec> {
    private final MonolithicExpr monolithicExpr;
    private final List<Frame> frames;
    private final UCSolver solver;

    private final Function<Valuation, S> valToState;
    private final BiFunction<Valuation, Valuation, A> biValToAction;

    private final boolean formerFramesOpt;

    private final boolean unSatOpt;

    private final boolean notBOpt;
    private final boolean propagateOpt;
    private final boolean filterOpt;

    private final SolverFactory solverFactory;

    public ConnectedIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction) {
        this(monolithicExpr, solverFactory, valToState, biValToAction, true, true, true, true, true);
    }

    public ConnectedIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction, boolean formerFramesOpt, boolean unSatOpt, boolean notBOpt, boolean propagateOpt, boolean filterOpt) {
        this.monolithicExpr = monolithicExpr;
        this.valToState = valToState;
        this.biValToAction = biValToAction;
        this.formerFramesOpt = formerFramesOpt;
        this.unSatOpt = unSatOpt;
        this.notBOpt = notBOpt;
        this.propagateOpt = propagateOpt;
        this.filterOpt = filterOpt;
        frames = new ArrayList<>();
        solver = solverFactory.createUCSolver();
        this.solverFactory = solverFactory;
    }



    @Override
    public SafetyResult<EmptyWitness, Trace<S, A>> check(UnitPrec prec) {
        //check if init violates prop
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
            solver.track(PathUtils.unfold(Not(monolithicExpr.getPropExpr()), 0));
            if (solver.check().isSat()) {
                return SafetyResult.unsafe(Trace.of(List.of(valToState.apply(solver.getModel())), List.of()), EmptyWitness.getInstance());
                // return null; //todo mutablevaluation itt is létrehoz
            }
        }

        StepIc3Checker forward = new StepIc3Checker(monolithicExpr, solverFactory,formerFramesOpt,unSatOpt,notBOpt,propagateOpt,filterOpt);

        ExprReverser exprReverser = new ExprReverser();

        MonolithicExpr reverseMonolithicExpr = new MonolithicExpr(Not(monolithicExpr.getPropExpr()), exprReverser.reverse(monolithicExpr.getTransExpr()), Not(monolithicExpr.getInitExpr()), monolithicExpr.getTransOffsetIndex());

        StepIc3Checker backward = new StepIc3Checker(reverseMonolithicExpr, solverFactory,formerFramesOpt,unSatOpt,notBOpt,propagateOpt,filterOpt);

        if(!forward.checkFirst() || !backward.checkFirst()){
            return SafetyResult.unsafe(null, EmptyWitness.getInstance());
        }
        while (true) {
           var counterExample = forward.checkCurrentFrame(And(backward.getcurrentFrame()));
           if(counterExample==null){
               if(forward.propagate()){
                   return SafetyResult.safe(EmptyWitness.getInstance());
               }
           }else{
               Boolean isBlocked = forward.tryBlock(new ProofObligation(new HashSet<>(counterExample), forward.getCurrentFrameNumber()));
               if(!isBlocked){
                   if(!backward.tryBlock(new ProofObligation(new HashSet<>(counterExample), backward.getCurrentFrameNumber()))){
                       return SafetyResult.unsafe(null, EmptyWitness.getInstance());
                   }
               }
           }
           counterExample = backward.checkCurrentFrame(Not(And(forward.getcurrentFrame())));
           if(counterExample==null){
               if(backward.propagate()){
                   return SafetyResult.safe(EmptyWitness.getInstance());
               }
           }else{
               Boolean isBlocked = backward.tryBlock(new ProofObligation(new HashSet<>(counterExample), backward.getCurrentFrameNumber()));
               if(!isBlocked){
                   if(!forward.tryBlock(new ProofObligation(new HashSet<>(counterExample), forward.getCurrentFrameNumber()))){
                       return SafetyResult.unsafe(null, EmptyWitness.getInstance());
                   }
               }
           }


//            if(forward.getCounterExample() == null){
//                forward.setProp(Not(And(backward.getcurrentFrame())));
//            }

//            Set<Expr<BoolType>> counterExample = forward.step(prec);
//            if(counterExample != null){
//                backward.setCounterExample(counterExample);
//                if(forward.isFaulty()){
//                    return SafetyResult.unsafe();
//                }
//            }else if(forward.isSafe()) {
//                return SafetyResult.safe();
//            }
//
//            if(backward.getCounterExample() == null) {
//                backward.setProp(Not(And(forward.getcurrentFrame())));
//            }
//
//
//            counterExample = backward.step(prec);
//            if(counterExample != null){
//                forward.setCounterExample(counterExample);
//                if(backward.isFaulty()){
//                    return SafetyResult.unsafe();
//                }
//            }else if(backward.isSafe()) {
//                return SafetyResult.safe();
//            }

        }
    }
}
