package hu.bme.mit.theta.analysis.algorithm.ic3;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.EmptyWitness;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.algorithm.bounded.ReversedMonolithicExprKt;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;

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
    private final boolean propertyOpt;
    private final boolean blockOpt;

    private final int forwardStep;

    private final int reverseStep;

    private final int forwardFrameOffset;

    private final int reverseFrameOffset;

    private final SolverFactory solverFactory;

    public ConnectedIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction) {
        this(monolithicExpr, solverFactory, valToState, biValToAction, true, true, true, true, true, true,true,1,1,0,0);
    }

    public ConnectedIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction, boolean formerFramesOpt, boolean unSatOpt, boolean notBOpt, boolean propagateOpt, boolean filterOpt, boolean propertyOpt, boolean blockOpt, int forwardStep, int reverseStep, int forwardFrameOffset, int reverseFrameOffset) {
        this.monolithicExpr = monolithicExpr;
        this.valToState = valToState;
        this.biValToAction = biValToAction;
        this.formerFramesOpt = formerFramesOpt;
        this.unSatOpt = unSatOpt;
        this.notBOpt = notBOpt;
        this.propagateOpt = propagateOpt;
        this.filterOpt = filterOpt;
        this.blockOpt = blockOpt;
        frames = new ArrayList<>();
        solver = solverFactory.createUCSolver();
        this.solverFactory = solverFactory;
        this.propertyOpt = propertyOpt;
        this.forwardStep = forwardStep;
        this.reverseStep = reverseStep;
        this.forwardFrameOffset = forwardFrameOffset;
        this.reverseFrameOffset = reverseFrameOffset;
    }




//    public SafetyResult<EmptyWitness, Trace<S, A>> check2(UnitPrec prec) {
//        //check if init violates prop
//        try (var wpp = new WithPushPop(solver)) {
//            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
//            solver.track(PathUtils.unfold(Not(monolithicExpr.getPropExpr()), 0));
//            if (solver.check().isSat()) {
//                return SafetyResult.unsafe(Trace.of(List.of(valToState.apply(solver.getModel())), List.of()), EmptyWitness.getInstance());
//                // return null; //todo mutablevaluation itt is létrehoz
//            }
//        }
//
//        //StepIc3Checker forward = new StepIc3Checker(monolithicExpr, solverFactory,formerFramesOpt,unSatOpt,notBOpt,propagateOpt,filterOpt);
//        Ic3Checker forward = new Ic3Checker<>(
//                monolithicExpr,
//                true,
//                Z3LegacySolverFactory.getInstance(),
//                valToState,
//                biValToAction,
//                formerFramesOpt,
//                unSatOpt,
//                notBOpt,
//                propagateOpt,
//                filterOpt,
//                propertyOpt,
//                blockOpt);
//        MonolithicExpr reverseMonolithicExpr = ReversedMonolithicExprKt.createReversed(monolithicExpr);
//
//        Ic3Checker backward = new Ic3Checker<>(
//                reverseMonolithicExpr,
//                false,
//                Z3LegacySolverFactory.getInstance(),
//                valToState,
//                biValToAction,
//                formerFramesOpt,
//                unSatOpt,
//                notBOpt,
//                propagateOpt,
//                filterOpt,
//                propertyOpt,
//                blockOpt);
//        //StepIc3Checker backward = new StepIc3Checker(reverseMonolithicExpr, solverFactory,formerFramesOpt,unSatOpt,notBOpt,propagateOpt,filterOpt);
//
////        if(!forward.checkFirst() || !backward.checkFirst()){
////            return SafetyResult.unsafe(null, EmptyWitness.getInstance());
////        } todo add checkFirst
////        while (true) {
////           var counterExample = forward.checkCurrentFrame(And(backward.getcurrentFrame()));
////           if(counterExample==null){
////               if(forward.propagate()){
////                   return SafetyResult.safe(EmptyWitness.getInstance());
////               }
////           }else{
////               var forwardProofObligations = forward.tryBlock(new ProofObligation(new HashSet<>(counterExample), forward.getCurrentFrameNumber()+1));
////               if(forwardProofObligations != null){
////                   var backwardProofObligations = backward.tryBlock(new ProofObligation(new HashSet<>(counterExample), backward.getCurrentFrameNumber()));
////                   if(null != backwardProofObligations){
////                       return SafetyResult.unsafe(traceMaker(backwardProofObligations,forwardProofObligations), EmptyWitness.getInstance());
////                   }
////               }
////           }
////           //counterExample = backward.checkCurrentFrame(Not(And(forward.getcurrentFrame())));
////           counterExample = backward.checkCurrentFrame(And(forward.getcurrentFrame()));
////           if(counterExample==null){
////               if(backward.propagate()){
////                   return SafetyResult.safe(EmptyWitness.getInstance());
////               }
////           }else{
////               var backwardProofObligations = backward.tryBlock(new ProofObligation(new HashSet<>(counterExample), backward.getCurrentFrameNumber()+1));
////               if(backwardProofObligations != null){
////                   //counterExample = getConjuncts(Not(And(counterExample)));
////                   var forwardProofobligations= forward.tryBlock(new ProofObligation(new HashSet<>(counterExample), forward.getCurrentFrameNumber()));
////                   if(null != forwardProofobligations){
////                       return SafetyResult.unsafe(traceMaker(backwardProofObligations,forwardProofobligations), EmptyWitness.getInstance());
////                   }
////               }
////           }
////
////        }
//        try (var wpp = new WithPushPop(solver)) {
//            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
//            solver.track(PathUtils.unfold(Not(monolithicExpr.getPropExpr()), 0));
//            if (solver.check().isSat()) {
//                return SafetyResult.unsafe(Trace.of(List.of(valToState.apply(solver.getModel())), List.of()), EmptyWitness.getInstance());
//                // return null; //todo mutablevaluation itt is létrehoz
//            }
//        }
//        while (true) {
//           var forwardCounterExample = forward.checkCurrentFrame(And(backward.getcurrentFrame(reverseFrameOffset)));
//           if(forwardCounterExample==null){
//               if(forward.propagate(null)){
//                   return SafetyResult.safe(EmptyWitness.getInstance());
//               }
//           }else{
//               var forwardProofObligations = forward.tryBlock(new ProofObligation(new HashSet<>(forwardCounterExample), forward.getCurrentFrameNumber()+1));
//               Collection backwardCounterExample;
//               if (propertyOpt) {
//                   backwardCounterExample = backward.checkCurrentFrame(And(forwardCounterExample));
//               } else {
//                   backwardCounterExample = backward.checkCurrentFrame(And(forward.getcurrentFrame()));
//               }
//               LinkedList backwardProofObligations = null;
//               if(backwardCounterExample!=null){
//                   backwardProofObligations = backward.tryBlock(new ProofObligation(new HashSet<>(backwardCounterExample), backward.getCurrentFrameNumber()));
//               }
//               if(forwardProofObligations != null && backwardProofObligations != null){
//                   return SafetyResult.unsafe(traceMaker(backwardProofObligations,forwardProofObligations), EmptyWitness.getInstance());
//               }
//           }
//        }
//    }


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

        //StepIc3Checker forward = new StepIc3Checker(monolithicExpr, solverFactory,formerFramesOpt,unSatOpt,notBOpt,propagateOpt,filterOpt);
        Ic3Checker forward = new Ic3Checker<>(
                monolithicExpr,
                true,
                Z3LegacySolverFactory.getInstance(),
                valToState,
                biValToAction,
                formerFramesOpt,
                unSatOpt,
                notBOpt,
                propagateOpt,
                filterOpt,
                propertyOpt,
                blockOpt);
        MonolithicExpr reverseMonolithicExpr = ReversedMonolithicExprKt.createReversed(monolithicExpr);

        Ic3Checker backward = new Ic3Checker<>(
                reverseMonolithicExpr,
                false,
                Z3LegacySolverFactory.getInstance(),
                valToState,
                biValToAction,
                formerFramesOpt,
                unSatOpt,
                notBOpt,
                propagateOpt,
                filterOpt,
                propertyOpt,
                blockOpt);
        if(blockOpt){
            while (true) {
                Collection counterExample;
                for(int i=0;i<forwardStep;i++){
                    counterExample = forward.checkCurrentFrame(And(backward.getcurrentFrame(reverseFrameOffset)));
                    if(counterExample==null){
                        if(forward.propagate(null)){
                            return SafetyResult.safe(EmptyWitness.getInstance());
                        }
                    }else{
                        var proofList = new ArrayList<Set<Expr<BoolType>>>();
                        proofList.add(new HashSet<>(counterExample));
                        var forwardProofObligations = forward.tryBlockMultiple(new MultipleProofObligation(proofList, forward.getCurrentFrameNumber(0)));
                        if(forwardProofObligations != null){
                            while(true){
                                var backwardCounterExample = backward.checkFrame(And(counterExample), backward.getCurrentFrameNumber(reverseFrameOffset));
                                if(backwardCounterExample == null){
                                    break;
                                }
                                var backwardProofList = new ArrayList<Set<Expr<BoolType>>>();
                                backwardProofList.add(new HashSet<>(backwardCounterExample));
                                var backwardProofObligations = backward.tryBlockMultiple(new MultipleProofObligation(backwardProofList, backward.getCurrentFrameNumber(reverseFrameOffset)));
                                if(backwardProofObligations != null){
                                    return SafetyResult.unsafe(forward.traceMakerMultiple(forwardProofObligations), EmptyWitness.getInstance());
                                }
                            }

                        }
                    }
                }
                for(int i=0;i<reverseStep;i++){
                    counterExample = backward.checkCurrentFrame(And(forward.getcurrentFrame(forwardFrameOffset)));
                    if(counterExample==null){
                        if(backward.propagate(null)){
                            return SafetyResult.safe(EmptyWitness.getInstance());
                        }
                    }else{
                        var proofList = new ArrayList<Set<Expr<BoolType>>>();
                        proofList.add(new HashSet<>(counterExample));
                        var backwardProofObligations = backward.tryBlockMultiple(new MultipleProofObligation(proofList, backward.getCurrentFrameNumber(0)));
                        if(backwardProofObligations != null){
                            while(true){
                                var forwardCounterExample = forward.checkFrame(And(counterExample), forward.getCurrentFrameNumber(forwardFrameOffset));
                                if(forwardCounterExample == null){
                                    break;
                                }
                                var forwardProofList = new ArrayList<Set<Expr<BoolType>>>();
                                forwardProofList.add(new HashSet<>(forwardCounterExample));
                                var forwardProofobligations= forward.tryBlockMultiple(new MultipleProofObligation(forwardProofList, forward.getCurrentFrameNumber(forwardFrameOffset)));
                                if(null != forwardProofobligations){
                                    return SafetyResult.unsafe(forward.traceMakerMultiple(backwardProofObligations), EmptyWitness.getInstance());
                                }
                            }
                        }
                    }
                }


            }
        }else{
            while (true) {
                Collection counterExample;
                for(int i=0;i<forwardStep;i++){
                    counterExample = forward.checkCurrentFrame(And(backward.getcurrentFrame(reverseFrameOffset)));
                    if(counterExample==null){
                        if(forward.propagate(null)){
                            return SafetyResult.safe(EmptyWitness.getInstance());
                        }
                    }else{

                        var forwardProofObligations = forward.tryBlock(new ProofObligation(new HashSet<>(counterExample), forward.getCurrentFrameNumber(0)));
                        if(forwardProofObligations != null){
                            while(true){
                                var backwardCounterExample = backward.checkFrame(And(counterExample), backward.getCurrentFrameNumber(reverseFrameOffset));
                                if(backwardCounterExample == null){
                                    break;
                                }
                                var backwardProofObligations = backward.tryBlock(new ProofObligation(new HashSet<>(backwardCounterExample), backward.getCurrentFrameNumber(reverseFrameOffset)));
                                if(backwardProofObligations != null){
                                    return SafetyResult.unsafe(traceMaker(backwardProofObligations,forwardProofObligations), EmptyWitness.getInstance());
                                }
                            }

                        }
                    }
                }
                for(int i=0;i<reverseStep;i++){
                    counterExample = backward.checkCurrentFrame(And(forward.getcurrentFrame(forwardFrameOffset)));
                    if(counterExample==null){
                        if(backward.propagate(null)){
                            return SafetyResult.safe(EmptyWitness.getInstance());
                        }
                    }else{
                        var backwardProofObligations = backward.tryBlock(new ProofObligation(new HashSet<>(counterExample), backward.getCurrentFrameNumber(0)));
                        if(backwardProofObligations != null){
                            while(true){
                                var forwardCounterExample = forward.checkFrame(And(counterExample), forward.getCurrentFrameNumber(forwardFrameOffset));
                                if(forwardCounterExample == null){
                                    break;
                                }
                                var forwardProofobligations= forward.tryBlock(new ProofObligation(new HashSet<>(forwardCounterExample), forward.getCurrentFrameNumber(forwardFrameOffset)));
                                if(null != forwardProofobligations){
                                    return SafetyResult.unsafe(traceMaker(backwardProofObligations,forwardProofobligations), EmptyWitness.getInstance());
                                }
                            }
                        }
                    }
                }


            }
        }


    }




    public Trace<S, A> traceMaker(LinkedList<ProofObligation> backwardProofObligations, LinkedList<ProofObligation> forwardProofObligations){
        var stateList= new ArrayList<S>();
        var actionList = new ArrayList<A>();
        Valuation lastValuation = null;

            forwardProofObligations.removeLast();
            MutableValuation mutableValuation = new MutableValuation();



        stateList.add(valToState.apply(mutableValuation));
//        while(!forwardProofObligations.isEmpty()) {
//            final ProofObligation currentProofObligation = forwardProofObligations.getLast();
//            forwardProofObligations.removeLast();
//            MutableValuation mutableValuation = new MutableValuation();
//            for (Expr<BoolType> ex : currentProofObligation.getExpressions()) {
//
//                RefExpr<BoolType> refExpr = (RefExpr<BoolType>) ex.getOps().get(0);
//                LitExpr<BoolType> litExpr = (LitExpr<BoolType>) ex.getOps().get(1);
//                mutableValuation.put(refExpr.getDecl(), litExpr);
//
//            }
//            stateList.add(valToState.apply(mutableValuation));
//            if (lastValuation != null) {
//                actionList.add(biValToAction.apply(lastValuation,mutableValuation));
//            }
//            lastValuation=mutableValuation;
//
//        }
//        backwardProofObligations.removeFirst();
//        while(!backwardProofObligations.isEmpty()) {
//            ProofObligation currentProofObligation = backwardProofObligations.getFirst();
//            backwardProofObligations.removeFirst();
//            MutableValuation mutableValuation = new MutableValuation();
//            for (Expr<BoolType> ex : currentProofObligation.getExpressions()) {
//
//                RefExpr<BoolType> refExpr = (RefExpr<BoolType>) ex.getOps().get(0);
//                LitExpr<BoolType> litExpr = (LitExpr<BoolType>) ex.getOps().get(1);
//                mutableValuation.put(refExpr.getDecl(), litExpr);
//
//            }
//            stateList.add(valToState.apply(mutableValuation));
//            if (lastValuation != null) {
//                actionList.add(biValToAction.apply(lastValuation,mutableValuation));
//            }
//            lastValuation=mutableValuation;
//
//        }
        return Trace.of(stateList,actionList);
    }
}


