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
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

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

    public Ic3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction) {
        this(monolithicExpr, solverFactory, valToState, biValToAction, true, true, true, true, true);
    }

    public Ic3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, Function<Valuation, S> valToState, BiFunction<Valuation, Valuation, A> biValToAction, boolean formerFramesOpt, boolean unSatOpt, boolean notBOpt, boolean propagateOpt, boolean filterOpt) {
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

        //create 0. frame
        frames.add(new Frame(null, solver, monolithicExpr));
        frames.get(0).refine(monolithicExpr.getInitExpr());

        frames.add(new Frame(frames.get(0), solver, monolithicExpr));
        int i = 1;
        while (true) {

            final Frame currentFrame = frames.get(i);
            final Collection<Expr<BoolType>> counterExample = currentFrame.check(Not(monolithicExpr.getPropExpr()));


            if (counterExample != null) {
                Trace<S, A> trace = tryBlock(new ProofObligation(new HashSet<>(counterExample), i));
                if (trace != null) {
                    return SafetyResult.unsafe(trace, EmptyWitness.getInstance());
                }
            } else {
                frames.add(new Frame(frames.get(i), solver, monolithicExpr));
                i++;
                if(propagateOpt){
                    for(int j=1;j<i;j++){
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
                            return SafetyResult.safe(EmptyWitness.getInstance());
                        }
                    }
                } else if(frames.get(i-1).equalsParent()){
                    return SafetyResult.safe(EmptyWitness.getInstance());
                }

            }
        }
    }

    Trace<S, A> tryBlock(ProofObligation mainProofObligation) {
        final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<ProofObligation>();
        proofObligationsQueue.add(mainProofObligation);
        while (!proofObligationsQueue.isEmpty()) {
            final ProofObligation proofObligation = proofObligationsQueue.getLast();

            if (proofObligation.getTime() == 0) {
                var stateList= new ArrayList<S>();
                var actionList = new ArrayList<A>();

                MutableValuation mutableValuation=new MutableValuation();
                for(Expr<BoolType> ex : proofObligation.getExpressions()){

                    RefExpr<BoolType> refExpr = (RefExpr<BoolType>) ex.getOps().get(0);
                    LitExpr<BoolType> litExpr = (LitExpr<BoolType>) ex.getOps().get(1);
                    mutableValuation.put(refExpr.getDecl(), litExpr);

                }

                stateList.add(valToState.apply(mutableValuation));

                return Trace.of(stateList,actionList);
            }

            final Collection<Expr<BoolType>> b;
            final Collection<Expr<BoolType>> unSatCore;

            try (var wpp = new WithPushPop(solver)) {

                frames.get(proofObligation.getTime() - 1).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                if(notBOpt){
                    solver.track(PathUtils.unfold(Not(And(proofObligation.getExpressions())),0));
                }
                if (proofObligation.getTime() > 2 && formerFramesOpt){ //lehet, hogy 1, vagy 2??
                    solver.track(PathUtils.unfold(Not(And(frames.get(proofObligation.getTime() - 2).getExprs())),0)); //2 vel korábbi frame-ban levő dolgok
                }

                getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation.getExpressions().forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));

                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();

                    if(filterOpt){
                        final MutableValuation filteredModel = new MutableValuation();
                        monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                        monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.getTransOffsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                        b = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(filteredModel, 0).toExpr(), 0));
                    }else{
                        b = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(model, 0).toExpr(), 0));
                    }

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
                    frames.get(i).refine(SmartBoolExprs.Not(And(newCore))); //mindegyik framehez hozzáadjuk a formulát
                }
                proofObligationsQueue.removeLast();
            } else {
                proofObligationsQueue.add(new ProofObligation(new HashSet<>(b), proofObligation.getTime() - 1));
            }
        }
        return null;

    }

    /*private boolean tryblock(Expr<BoolType> b,int n){
        if(n<=0){
            return false;
        }
        Solver solver = F.get(n-1);

        final SolverStatus status;
        final boolean couldBlock;
        try (var wpp = new WithPushPop(solver)) {
            solver.add(PathUtils.unfold(sts.getTrans(), n - 1));
            solver.add(PathUtils.unfold(b, n));
            status = solver.check();
            couldBlock = status.isUnsat() || tryblock(solver.getModel().toExpr(), n - 1);
        }

        if(couldBlock){
            F.get(n).add(Not(b));
            return true;
        } else {
            return false;
        }
    }*/
}
