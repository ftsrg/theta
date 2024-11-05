package hu.bme.mit.theta.analysis.algorithm.ic3;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.EmptyWitness;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
//import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;
//import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
//import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;
import static hu.bme.mit.theta.core.utils.ExprUtils.transformEquiSatCnf;

public class Ic3Checker<S extends ExprState, A extends ExprAction> implements SafetyChecker<EmptyWitness, Trace<S, A>, UnitPrec> {
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
    private int currentFrameNumber;

    private final boolean forwardTrace;
    private final boolean propertyOpt;

    private final boolean blockOpt;

    public Set<Expr<BoolType>> getcurrentFrame(int offset) {
        if(offset == -1){
            return frames.get(0).getExprs();
        }
        if(currentFrameNumber - offset < 0){
            return frames.get(0).getExprs();
        }
        return frames.get(currentFrameNumber-offset).getExprs();
    }

    public int getCurrentFrameNumber(int offset) {
        if(offset == -1){
            return 0;
        }
        if(currentFrameNumber- offset < 0){
            return 0;
        }
        return currentFrameNumber-offset;
    }

    public Ic3Checker(MonolithicExpr monolithicExpr, boolean forwardTrace, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction, boolean blockOpt) {
        this(monolithicExpr, forwardTrace,solverFactory, valToState, biValToAction, true, true, true, true, true, false, blockOpt);
    }

    public Ic3Checker(MonolithicExpr monolithicExpr, boolean forwardTrace, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction, boolean formerFramesOpt, boolean unSatOpt, boolean notBOpt, boolean propagateOpt, boolean filterOpt, boolean propertyOpt, boolean blockOpt) {
        this.monolithicExpr = monolithicExpr;
        this.valToState = valToState;
        this.biValToAction = biValToAction;
        this.formerFramesOpt = formerFramesOpt;
        this.unSatOpt = unSatOpt;
        this.notBOpt = notBOpt;
        this.propagateOpt = propagateOpt;
        this.filterOpt = filterOpt;
        this.forwardTrace = forwardTrace;
        this.propertyOpt = propertyOpt;
        this.blockOpt = blockOpt;
        frames = new ArrayList<>();
        solver = solverFactory.createUCSolver();
        frames.add(new Frame(null, solver, monolithicExpr));
        frames.get(0).refine(monolithicExpr.getInitExpr());
        currentFrameNumber = 0;
    }



    @Override
    public SafetyResult<EmptyWitness, Trace<S, A>> check(UnitPrec prec) {
        //check if init violates prop
        var firstTrace = checkFirst();
       if (firstTrace != null) {
           return SafetyResult.unsafe(firstTrace, EmptyWitness.getInstance());
        }
        //create 0. frame


        //frames.add(new Frame(frames.get(0), solver, monolithicExpr));

        while (true) {

            final Frame currentFrame = frames.get(currentFrameNumber);
            final Collection<Expr<BoolType>> counterExample =  checkCurrentFrame(Not(monolithicExpr.getPropExpr()));
            //final Collection<Expr<BoolType>> counterExample = currentFrame.check(Not(monolithicExpr.getPropExpr()));


            if (counterExample != null) {
                //Trace<S, A> trace = tryBlock(new ProofObligation(new HashSet<>(counterExample), currentFrameNumber));
                //var proofObligationLinkedList = tryBlock(new ProofObligation(new HashSet<>(counterExample), currentFrameNumber));


                if(blockOpt){
                    var proofList = new ArrayList<Set<Expr<BoolType>>>();
                    proofList.add(new HashSet<>(counterExample));

                    var proofObligationLinkedList = tryBlockMultiple(new MultipleProofObligation(proofList, currentFrameNumber));
                    if (proofObligationLinkedList != null) {
                        var trace = traceMakerMultiple(proofObligationLinkedList);
                        //var trace = traceMaker(new LinkedList<ProofObligation>(),proofObligationLinkedList);
                        return SafetyResult.unsafe(trace, EmptyWitness.getInstance());
                    }
                }else{
                    var proofObligationsList = tryBlock(new ProofObligation(new HashSet<>(counterExample), currentFrameNumber));
                    if (proofObligationsList != null) {
                        var trace = traceMaker(new LinkedList<ProofObligation>(),proofObligationsList);
                        return SafetyResult.unsafe(trace, EmptyWitness.getInstance());
                    }

                }

            } else {
                if(propagate(null)){
                    return SafetyResult.safe(EmptyWitness.getInstance());
                }
            }
        }
    }

    LinkedList<MultipleProofObligation> tryBlockMultiple(MultipleProofObligation mainProofObligation) {
        final LinkedList<MultipleProofObligation> proofObligationsQueue = new LinkedList<MultipleProofObligation>();
        proofObligationsQueue.add(mainProofObligation);
        while (!proofObligationsQueue.isEmpty()) {
            final MultipleProofObligation proofObligationsList = proofObligationsQueue.getLast();

            if (proofObligationsList.getTime() == 0) {
                return proofObligationsQueue;
//                var stateList= new ArrayList<S>();
//                var actionList = new ArrayList<A>();
//                Valuation lastValuation = null;
//                while(!proofObligationsQueue.isEmpty()) {
//                    final ProofObligation currentProofObligation = proofObligationsQueue.getLast();
//                    proofObligationsQueue.removeLast();
////                    final ProofObligation currentProofObligation = proofObligationsQueue.getFirst();
////                    proofObligationsQueue.removeFirst();
//                    MutableValuation mutableValuation = new MutableValuation();
//                    for (Expr<BoolType> ex : currentProofObligation.getExpressions()) {
//
//                        RefExpr<BoolType> refExpr = (RefExpr<BoolType>) ex.getOps().get(0);
//                        LitExpr<BoolType> litExpr = (LitExpr<BoolType>) ex.getOps().get(1);
//                        mutableValuation.put(refExpr.getDecl(), litExpr);
//
//                    }
//                    stateList.add(valToState.apply(mutableValuation));
//                    if (lastValuation != null) {
//                        actionList.add(biValToAction.apply(lastValuation,mutableValuation));
//                    }
//                    lastValuation=mutableValuation;
//
//                }
//                return Trace.of(stateList,actionList);
            }

            final ArrayList<Set<Expr<BoolType>>> b;

            Collection<Expr<BoolType>> unSatCore = null;
            Expr currentExpression = null;
            Collection<Expr<BoolType>> currentExpressionList = new ArrayList<>();
            for(var bi : proofObligationsList.getExpressionsList()){
                currentExpressionList.add(And(bi));
            }
            currentExpression = Or(currentExpressionList);
            try (var wpp = new WithPushPop(solver)) {
                frames.get(proofObligationsList.getTime() - 1).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                if(notBOpt){
                    solver.track(PathUtils.unfold(Not(currentExpression),0)); //?? ez jó?
                }
                if (proofObligationsList.getTime() > 2 && formerFramesOpt){ //lehet, hogy 1, vagy 2??
                    solver.track(PathUtils.unfold(Not(And(frames.get(proofObligationsList.getTime() - 2).getExprs())),monolithicExpr.getTransOffsetIndex())); //2 vel korábbi frame-ban levő dolgok
                }

                getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));

                //currentExpressionList.forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));
                solver.track(PathUtils.unfold(currentExpression, monolithicExpr.getTransOffsetIndex()));

                if (solver.check().isSat()) {
                    b = new ArrayList<>();
                    int i = 0;
                    do {
                        final Valuation model = solver.getModel();
                        final Collection<Expr<BoolType>> current;

                        final MutableValuation filteredModel = new MutableValuation();
                        monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                        //monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.getTransOffsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));

                        if(filterOpt){
                            var vars = new HashSet<>(filteredModel.toMap().keySet());
                            for(var var: vars){
                                if(!(var.getType() instanceof BoolType)){
                                    continue;
                                }
                                var origValue = model.eval(var).get();
                                var negatedValue = BoolLitExpr.of(!((BoolLitExpr) origValue).getValue());
                                filteredModel.put(var, negatedValue);
                                try (var wpp2 = new WithPushPop(solver)) {
                                    solver.track(PathUtils.unfold(filteredModel.toExpr(), 0));
                                    if (solver.check().isSat()) {
                                        filteredModel.remove(var);
                                    } else {
                                        filteredModel.put(var, origValue);
                                    }
                                }
                            }
                        }

                        current = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(filteredModel, 0).toExpr(), 0));


                        int finalI = i;
                        b.add(new HashSet<>());
                        current.forEach(ex -> b.get(finalI).add(ex));
                        solver.track(PathUtils.unfold(Not(And(current)),0));
                        i++;
                    }while(blockOpt && solver.check().isSat() && i<3);

                    unSatCore = null;
                } else {
                    b = null;
                }
            }
            if (b == null) {
                for(var bi : proofObligationsList.getExpressionsList()){
                    final Collection<Expr<BoolType>> newCore = new ArrayList<Expr<BoolType>>();
                    newCore.addAll(bi);
                    if(unSatOpt){
                        try (var wpp = new WithPushPop(solver)) {
                            frames.get(proofObligationsList.getTime() - 1).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
//                            if(notBOpt){
//                                //solver.track(PathUtils.unfold(Not(currentExpression),0)); // ide esetleg bi-t????
//                                solver.track(PathUtils.unfold(Not(currentExpression),0)); //?? ez jó?
//                            }
                            if (proofObligationsList.getTime() > 2 && formerFramesOpt){ //lehet, hogy 1, vagy 2??
                                solver.track(PathUtils.unfold(Not(And(frames.get(proofObligationsList.getTime() - 2).getExprs())),monolithicExpr.getTransOffsetIndex())); //2 vel korábbi frame-ban levő dolgok
                            }

                            getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));

                            //currentExpressionList.forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));
                            bi.forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));

                            if(solver.check().isUnsat()){
                                unSatCore = solver.getUnsatCore();
                            }else{
                                throw new RuntimeException("Unexpected sat result");
                            }
                        }
                        for (Expr<BoolType> i : bi) {
                            if (!unSatCore.contains(PathUtils.unfold(i, monolithicExpr.getTransOffsetIndex()))) {
                                newCore.remove(i);
                                final boolean isSat;
                                try (var wpp = new WithPushPop(solver)) {
                                    for (Expr<BoolType> solverex : newCore) {
                                        solver.track(PathUtils.unfold(solverex, 0));
                                    }
                                    solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
                                    isSat = solver.check().isSat();
                                }
                                if (isSat) {
                                    newCore.add(i);
                                }
                            }
                        }
                    }
                    for(int i = 1; i<=proofObligationsList.getTime(); ++i){
                        frames.get(i).refine(Not(And(newCore))); //mindegyik framehez hozzáadjuk a formulát
                    }
                }
//                for(int i = 1; i<=proofObligationsList.getTime(); ++i){
//                    for(var bi : proofObligationsList.getExpressionsList()){
//                        frames.get(i).refine(Not(currentExpression));
//                    }
//                    //mindegyik framehez hozzáadjuk a formulát
//                }
                proofObligationsQueue.removeLast();
            } else {
                proofObligationsQueue.add(new MultipleProofObligation(b, proofObligationsList.getTime() - 1));
            }
        }
        return null;

    }
    LinkedList<ProofObligation> tryBlock(ProofObligation mainProofObligation) {
        final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<ProofObligation>();
        proofObligationsQueue.add(mainProofObligation);
        while (!proofObligationsQueue.isEmpty()) {
            final ProofObligation proofObligation = proofObligationsQueue.getLast();

            if (proofObligation.getTime() == 0) {
                return proofObligationsQueue;
            }

            final Collection<Expr<BoolType>> b;
            final Collection<Expr<BoolType>> unSatCore;
            try (var wpp = new WithPushPop(solver)) {

                frames.get(proofObligation.getTime() - 1).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                if(notBOpt){
                    solver.track(PathUtils.unfold(Not(And(proofObligation.getExpressions())),0));
                }
                if (proofObligation.getTime() > 2 && formerFramesOpt){ //lehet, hogy 1, vagy 2??
                    solver.track(PathUtils.unfold(Not(And(frames.get(proofObligation.getTime() - 2).getExprs())),monolithicExpr.getTransOffsetIndex())); //2 vel korábbi frame-ban levő dolgok
                }

                getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation.getExpressions().forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));

                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();

                    final MutableValuation filteredModel = new MutableValuation();
                    monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                    //monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.getTransOffsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));

                    if(filterOpt){
                        var vars = new HashSet<>(filteredModel.toMap().keySet());
                        for(var var: vars){
                            if(!(var.getType() instanceof BoolType)){
                                continue;
                            }
                            var origValue = model.eval(var).get();
                            var negatedValue = BoolLitExpr.of(!((BoolLitExpr) origValue).getValue());
                            filteredModel.put(var, negatedValue);
                            try (var wpp2 = new WithPushPop(solver)) {
                                solver.track(PathUtils.unfold(filteredModel.toExpr(), 0));
                                if (solver.check().isSat()) {
                                    filteredModel.remove(var);
                                } else {
                                    filteredModel.put(var, origValue);
                                }
                            }
                        }
                    }


                    b = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(filteredModel, 0).toExpr(), 0));
                    unSatCore = null;
                } else {
                    b = null;
                    unSatCore = solver.getUnsatCore();
                }
            }
            if (b == null) {

                final Collection<Expr<BoolType>> newCore = new ArrayList<Expr<BoolType>>();
                newCore.addAll(proofObligation.getExpressions());
                if(unSatOpt){
                    for (Expr<BoolType> i : proofObligation.getExpressions()) {
                        if (!unSatCore.contains(PathUtils.unfold(i, monolithicExpr.getTransOffsetIndex()))) {
                            newCore.remove(i);
                            final boolean isSat;
                            try (var wpp = new WithPushPop(solver)) {
                                for (Expr<BoolType> solverex : newCore) {
                                    solver.track(PathUtils.unfold(solverex, 0));
                                }
                                solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
                                isSat = solver.check().isSat();
                            }
                            if (isSat) {
                                newCore.add(i);
                            }
                        }
                    }
                }
                for(int i = 1; i<=proofObligation.getTime(); ++i){
                    frames.get(i).refine(Not(And(newCore))); //mindegyik framehez hozzáadjuk a formulát
                }
                proofObligationsQueue.removeLast();
            } else {
                proofObligationsQueue.add(new ProofObligation(new HashSet<>(b), proofObligation.getTime() - 1));
            }
        }
        return null;

    }

    public Trace<S, A> checkFirst(){
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
            solver.track(PathUtils.unfold(Not(monolithicExpr.getPropExpr()), 0));
            if (solver.check().isSat()) {
                return Trace.of(List.of(valToState.apply(solver.getModel())), List.of());
            }
        }
        if(propertyOpt){
            try (var wpp = new WithPushPop(solver)) {
                solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
                solver.track(PathUtils.unfold(monolithicExpr.getTransExpr(), 0));
                solver.track(PathUtils.unfold(Not(monolithicExpr.getPropExpr()), monolithicExpr.getTransOffsetIndex()));
                if (solver.check().isSat()) {
                    //todo fix
                    return Trace.of(List.of(valToState.apply(solver.getModel())), List.of());
                }else {
                    return null;
                }
            }
        } else {
            return null;
        }

    }

    public Collection<Expr<BoolType>> checkCurrentFrame(Expr<BoolType> target){
        if (propertyOpt) {
            try (var wpp = new WithPushPop(solver)) {
                frames.get(currentFrameNumber).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                solver.track(PathUtils.unfold(target, monolithicExpr.getTransOffsetIndex()));
                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();
                    final MutableValuation filteredModel = new MutableValuation();
                    monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                    //monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.getTransOffsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                    return getConjuncts(PathUtils.foldin(filteredModel.toExpr(), 0));
                }else {
                    return null;
                }
            }
        } else {
            return frames.get(currentFrameNumber).check(target);
        }

    }
    public Collection<Expr<BoolType>> checkFrame(Expr<BoolType> target, int frameNumber){
        if (propertyOpt) {
            try (var wpp = new WithPushPop(solver)) {
                frames.get(frameNumber).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                solver.track(PathUtils.unfold(target, monolithicExpr.getTransOffsetIndex()));
                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();
                    final MutableValuation filteredModel = new MutableValuation();
                    monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                    //monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.getTransOffsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                    return getConjuncts(PathUtils.foldin(filteredModel.toExpr(), 0));
                }else {
                    return null;
                }
            }
        } else {
            return frames.get(frameNumber).check(target);
        }

    }

    public boolean propagate(Expr<BoolType> prop){
        frames.add(new Frame(frames.get(currentFrameNumber), solver, monolithicExpr));
        currentFrameNumber++;
        if(propertyOpt){
            for(int j=1; j<=currentFrameNumber;j++){
                frames.get(j).refine(monolithicExpr.getPropExpr());
            }
        }

        if(propagateOpt){
            for(int j=1;j<currentFrameNumber;j++){
                for(var c : frames.get(j).getExprs()){
                    try (var wpp = new WithPushPop(solver)) {
                        frames.get(j).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                        getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                        solver.track(PathUtils.unfold(Not(c), monolithicExpr.getTransOffsetIndex()));
                        if(solver.check().isUnsat()){
                            frames.get(j+1).refine(c);
                        }
                    }
                }
                if(frames.get(j+1).equalsParent()){
                    return true;
                }
            }
        } else if(currentFrameNumber>1 && frames.get(currentFrameNumber-1).equalsParent()){
            return true;
        }
        return false;
    }

    public Trace<S, A> traceMaker(LinkedList<ProofObligation> backwardProofObligations, LinkedList<ProofObligation> forwardProofObligations){
        var stateList= new ArrayList<S>();
        var actionList = new ArrayList<A>();
        Valuation lastValuation = null;

        while(!forwardProofObligations.isEmpty()) {
            final ProofObligation currentProofObligation;
            if(forwardTrace){
                currentProofObligation = forwardProofObligations.getLast();
                forwardProofObligations.removeLast();
            }else{
                currentProofObligation = forwardProofObligations.getFirst();
                forwardProofObligations.removeFirst();
            }


            MutableValuation mutableValuation = new MutableValuation();
            for (Expr<BoolType> ex : currentProofObligation.getExpressions()) {

                RefExpr<BoolType> refExpr = (RefExpr<BoolType>) ex.getOps().get(0);
                LitExpr<BoolType> litExpr = (LitExpr<BoolType>) ex.getOps().get(1);
                mutableValuation.put(refExpr.getDecl(), litExpr);

            }
            stateList.add(valToState.apply(mutableValuation));
            if (lastValuation != null) {
                actionList.add(biValToAction.apply(lastValuation,mutableValuation));
            }
            lastValuation=mutableValuation;

        }

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


    public Trace<S, A> traceMakerMultiple(LinkedList<MultipleProofObligation> forwardProofObligations){
        try (var wpp = new WithPushPop(solver)) {
            if (solver.check().isSat()) {
                return Trace.of(List.of(valToState.apply(solver.getModel())), List.of());
            }else {
                return null;
            }
        }
    }

}
