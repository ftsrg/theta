package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser;

import java.util.*;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

public class Ic3Checker implements SafetyChecker {
    private final MonolithicExpr monolithicExpr;
    private final List<Frame> frames;
    private final UCSolver solver;

    public Ic3Checker(MonolithicExpr monolithicExpr, SolverFactory solverFactory) {
        this.monolithicExpr = monolithicExpr;
        //F = new ArrayList<Solver>();
        frames = new ArrayList<>();
        solver = solverFactory.createUCSolver();
    }



    @Override
    public SafetyResult check(Prec prec) {
        //check if init violates prop
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(monolithicExpr.init(), 0));
            solver.track(PathUtils.unfold(Not(monolithicExpr.prop()), 0));
            if (solver.check().isSat()) {
                return null; //todo mutablevaluation itt is létrehoz
            }
        }

        //create 0. frame
        frames.add(new Frame(null, solver, monolithicExpr));
        frames.get(0).refine(monolithicExpr.init());

        frames.add(new Frame(frames.get(0), solver, monolithicExpr));
        int i = 1;
        while (true) {

            final Frame currentFrame = frames.get(i);
            final Collection<Expr<BoolType>> counterExample = currentFrame.check(Not(monolithicExpr.prop()));


            if (counterExample != null) {
//                if(!currentFrame.tryBlock(counterExample)){
//                    return false;
//                }
                Trace trace = tryBlock(new ProofObligation(counterExample, i));
                if (trace != null) {
                    return SafetyResult.unsafe(trace);
                }
            } else {

//                if (currentFrame.equalsParent()) {
//                    return SafetyResult.safe();
//                } else {

                frames.add(new Frame(frames.get(i), solver,monolithicExpr));
                i++;
                for(int j=1;j<i;j++){
                    for(var c : frames.get(j).getExprs()){
                        try (var wpp = new WithPushPop(solver)) {
                            frames.get(j).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                            solver.track(PathUtils.unfold(c, 0));
                            getConjuncts(monolithicExpr.trans()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                            solver.track(PathUtils.unfold(Not(c), monolithicExpr.offsetIndex()));
                            if(solver.check().isUnsat()){
                                frames.get(j+1).refine(c);
                            }
                        }
                    }
                    if(frames.get(j).equalsParent()){
                        return SafetyResult.safe();
                    }
                }
            }
        }
    }

    Trace tryBlock(ProofObligation mainProofObligation) {
        final LinkedList<ProofObligation> proofObligationsQueue = new LinkedList<ProofObligation>();
        ProofObligation proofObligation = mainProofObligation;
        while (true) {

            if (proofObligation.getTime() == 0) {
                STS sts = new STS(monolithicExpr.init(), monolithicExpr.trans(), monolithicExpr.prop());
                proofObligationsQueue.add(proofObligation);
                ArrayList<ExplState> explStateArrayList= new ArrayList<ExplState>();
                ArrayList<StsAction> stsActionArrayList = new ArrayList<StsAction>();
                while(!proofObligationsQueue.isEmpty()){
                    proofObligation = proofObligationsQueue.getLast();

                    proofObligationsQueue.removeLast();
                    MutableValuation mutableValuation=new MutableValuation();
                    for(Expr<BoolType> ex : proofObligation.getExpressions()){

                        RefExpr<BoolType> refExpr = (RefExpr<BoolType>) ex.getOps().get(0);
                        LitExpr<BoolType> litExpr = (LitExpr<BoolType>) ex.getOps().get(1);
                        mutableValuation.put(refExpr.getDecl(), litExpr);

                    }

                    explStateArrayList.add(ExplState.of(mutableValuation));
                    if (explStateArrayList.size()>1){

                        StsAction stsAction = new StsAction(sts);
                        stsActionArrayList.add(stsAction);
                    }
                }
                Trace trace = Trace.of(explStateArrayList,stsActionArrayList);
                return trace;
            }

            final Collection<Expr<BoolType>> b;
            final Collection<Expr<BoolType>> unSatCore;

            try (var wpp = new WithPushPop(solver)) {

                frames.get(proofObligation.getTime() - 1).getExprs().forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                solver.track(PathUtils.unfold(Not(And(proofObligation.getExpressions())),0));
                if (proofObligation.getTime() > 1){ //lehet, hogy 1, vagy 2??
                    solver.track(PathUtils.unfold(Not(And(frames.get(proofObligation.getTime() - 2).getExprs())),0)); //2 vel korábbi frame-ban levő dolgok
                }
                //proofObligation.getExpressions().forEach(ex -> solver.track(PathUtils.unfold(Not(ex), 0)));
                getConjuncts(monolithicExpr.trans()).forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
                proofObligation.getExpressions().forEach(ex -> solver.track(PathUtils.unfold(ex, monolithicExpr.offsetIndex())));

                if (solver.check().isSat()) {
                    final Valuation model = solver.getModel();
                    final MutableValuation filteredModel = new MutableValuation();
//                    var a = monolithicExpr.vars();
//                    var c = model.toMap();
//                    monolithicExpr.vars().stream().filter(model.toMap()::containsKey).forEach(decl -> System.out.println(decl));
                    monolithicExpr.vars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                    monolithicExpr.vars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.offsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
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
                for (Expr<BoolType> i : proofObligation.getExpressions()) {
                    if (!unSatCore.contains(PathUtils.unfold(i, monolithicExpr.offsetIndex()))) {
                        newCore.remove(i);
                        final boolean isSat;
                        try (var wpp = new WithPushPop(solver)) {
                            for (Expr<BoolType> solverex : newCore) {
                                solver.track(PathUtils.unfold(solverex, 0));
                            }
                            solver.track(PathUtils.unfold(monolithicExpr.init(), 0));
                            isSat = solver.check().isSat();
                        }
                        if (isSat) {
                            newCore.add(i);
                        }
                    }
                }
                for(int i = 1; i<=proofObligation.getTime(); ++i){
                    frames.get(i).refine(SmartBoolExprs.Not(And(newCore))); //mindegyik framehez hozzáadjuk a formulát
                }
                //frames.get(proofObligation.getTime()).refine(SmartBoolExprs.Not(And(newCore)));
                break;
            } else {
                proofObligationsQueue.add(proofObligation);
                proofObligation = new ProofObligation(b, proofObligation.getTime() - 1);
            }
        }
        while (!proofObligationsQueue.isEmpty()) {
            proofObligation = proofObligationsQueue.poll();
            for(int i = 1; i<=proofObligation.getTime(); ++i){
                frames.get(i).refine(Not(And(proofObligation.getExpressions()))); //mindegyik framehez hozzáadjuk a formulát
            }
            //frames.get(proofObligation.getTime()).refine(Not(And(proofObligation.getExpressions())));
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
