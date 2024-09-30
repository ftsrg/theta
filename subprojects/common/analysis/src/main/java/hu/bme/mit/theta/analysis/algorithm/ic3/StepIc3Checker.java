package hu.bme.mit.theta.analysis.algorithm.ic3;

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

public class StepIc3Checker{
    private final MonolithicExpr monolithicExpr;

    public Set<Expr<BoolType>> getcurrentFrame() {
        if(currentFrameNumber == 0){
            return frames.get(currentFrameNumber).getExprs();
        }
        return frames.get(currentFrameNumber-1).getExprs();
    }

    private final List<Frame> frames;
    private final UCSolver solver;

    private final boolean formerFramesOpt;

    private final boolean unSatOpt;

    private final boolean notBOpt;
    private final boolean propagateOpt;

    public Collection<Expr<BoolType>> getCounterExample() {
        return counterExample;
    }

    private final boolean filterOpt;

    public void setCounterExample(Set<Expr<BoolType>> counterExample) {
        this.counterExample = counterExample;
    }

    private Collection<Expr<BoolType>> counterExample;

    private final int stepcount = 1;

    public boolean isSafe() {
        return safe;
    }

    public void setSafe(boolean safe) {
        this.safe = safe;
    }
    private boolean safe = false;

    public boolean isFaulty() {
        return faulty;
    }

    private boolean faulty = false;

    public int getCurrentFrameNumber() {
        return currentFrameNumber;
    }

    public void setCurrentFrameNumber(int currentFrameNumber) {
        this.currentFrameNumber = currentFrameNumber;
    }

    private int currentFrameNumber;

    boolean checkingOtherCounterExample;


    public StepIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory) {
        this(monolithicExpr, solverFactory, true, true, true, true, true);
    }

    public StepIc3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory, boolean formerFramesOpt, boolean unSatOpt, boolean notBOpt, boolean propagateOpt, boolean filterOpt) {
        this.monolithicExpr = monolithicExpr;
        this.formerFramesOpt = formerFramesOpt;
        this.unSatOpt = unSatOpt;
        this.notBOpt = notBOpt;
        this.propagateOpt = propagateOpt;
        this.filterOpt = filterOpt;
        frames = new ArrayList<>();
        solver = solverFactory.createUCSolver();
        frames.add(new Frame(null, solver, monolithicExpr));
        frames.get(0).refine(monolithicExpr.getInitExpr());
        currentFrameNumber = 0;
    }
    public boolean checkFirst(){
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(), 0));
            solver.track(PathUtils.unfold(Not(monolithicExpr.getPropExpr()), 0));
            if (solver.check().isSat()) {
                return false;
            }else{
                return true;
            }
        }
    }

    public Collection<Expr<BoolType>> checkCurrentFrame(Expr<BoolType> target){
        return frames.get(currentFrameNumber).check(target);
    }

    public boolean propagate(){
        frames.add(new Frame(frames.get(currentFrameNumber), solver, monolithicExpr));
        currentFrameNumber++;
        //frames.get(currentFrameNumber).refine(prop); //todo korábbiakhot hozzáadni esetleg?
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
        } else if(frames.get(currentFrameNumber-1).equalsParent()){
            return true;
        }
        return false;
    }

    public Boolean tryBlock(ProofObligation mainProofObligation) {
        final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<ProofObligation>();
        proofObligationsQueue.add(mainProofObligation);
        while (!proofObligationsQueue.isEmpty()) {
            final ProofObligation proofObligation = proofObligationsQueue.getLast();

            if (proofObligation.getTime() == 0) {
                return false;
            }

            final Collection<Expr<BoolType>> b;
            final Collection<Expr<BoolType>> unSatCore;

            try (var wpp = new WithPushPop(solver)) {

                frames.get(proofObligation.getTime() - 1).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                if (notBOpt) {
                    solver.track(PathUtils.unfold(Not(And(proofObligation.getExpressions())), 0));
                }
                if (proofObligation.getTime() > 2 && formerFramesOpt) { //lehet, hogy 1, vagy 2??
                    solver.track(PathUtils.unfold(Not(And(frames.get(proofObligation.getTime() - 2).getExprs())), 0)); //2 vel korábbi frame-ban levő dolgok
                }

                getConjuncts(monolithicExpr.getTransExpr()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation.getExpressions().forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.getTransOffsetIndex())));

                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();

                    if (filterOpt) {
                        final MutableValuation filteredModel = new MutableValuation();
                        monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                        monolithicExpr.getVars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.getTransOffsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                        b = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(filteredModel, 0).toExpr(), 0));
                    } else {
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
                if (unSatOpt) {
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

                for (int i = 1; i <= proofObligation.getTime(); ++i) {
                    frames.get(i).refine(SmartBoolExprs.Not(And(newCore))); //mindegyik framehez hozzáadjuk a formulát
                }
                proofObligationsQueue.removeLast();
            } else {
                proofObligationsQueue.add(new ProofObligation(new HashSet<>(b), proofObligation.getTime() - 1));
            }
        }
        return true;
    }
}

