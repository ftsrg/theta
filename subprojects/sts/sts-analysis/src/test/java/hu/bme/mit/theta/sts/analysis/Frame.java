package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;

import hu.bme.mit.theta.solver.UCSolver;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;


public class Frame {
    private final Frame parent;
    private final ArrayList<Expr<BoolType>> exprs;

    private final UCSolver solver;
    private final MonolithicExpr monolithicExpr;

    Frame(final Frame parent, UCSolver solver, MonolithicExpr monolithicExpr) {
        this.parent = parent;
        this.solver = solver;
        this.monolithicExpr=monolithicExpr;
        exprs = new ArrayList<>();
    }

    public void refine(Expr<BoolType> expression) {
        //Expr<BoolType> cnfex = transformEquiSatCnf(expression);
        Collection<Expr<BoolType>> col = getConjuncts(expression);
        for (Expr<BoolType> e : col) {
            exprs.add(e);
        }
    }

//    public boolean tryBlock(Collection<Expr<BoolType>> e) {
//        if (parent == null) {
//            return false;
//        }
//        Collection
//                <Expr<BoolType>> b = null;
//        Expr<BoolType> be = null;
//
//
//        Collection<Expr<BoolType>> Unsatcol = null;
//        Collection<Expr<BoolType>> ecol = null;
//
//        Collection<Expr<BoolType>> unSatCore = null;
//        SolverStatus status;
//        try (var wpp = new WithPushPop(solver)) {
//
//            for (Expr<BoolType> ex : parent.getExprs()) {
//                solver.track(PathUtils.unfold(ex, 0));
//            }
//            ;
//            //transformEquiSatCnf
//            Collection<Expr<BoolType>> col = getConjuncts(trans);
//            for (Expr<BoolType> ex : col) {
//                solver.track(PathUtils.unfold(ex, 0));
//            }
//
//            for (Expr<BoolType> assertion : e) {
//                solver.track(PathUtils.unfold(assertion, 1));
//            }
//            status = solver.check();
//            if (status.isSat()) {
//
//                //b = PathUtils.foldin(PathUtils.extractValuation(solver.getModel(),0).toExpr(),0);
//                b = getConjuncts(PathUtils.foldin(PathUtils.extractValuation(solver.getModel(), 0).toExpr(), 0));
//
//            } else {
//                unSatCore = solver.getUnsatCore();
//
//
//            }
//        }
//        boolean couldBlock = b == null || parent.tryBlock(b);
//        if (couldBlock) {
//            Collection<Expr<BoolType>> newCore = new ArrayList<Expr<BoolType>>();
//            ;
//            if (unSatCore != null) {
//                newCore.addAll(e);
//                for (Expr<BoolType> i : e) {
//                    if (!unSatCore.contains(PathUtils.unfold(i, 1))) {
//                        newCore.remove(i);
//                        boolean isSat;
//                        try (var wpp = new WithPushPop(solver)) {
//                            for (Expr<BoolType> solverex : newCore) {
//                                solver.track(PathUtils.unfold(solverex, 0));
//                            }
//                            solver.track(PathUtils.unfold(init, 0));
//                            isSat = solver.check().isSat();
//                        }
//                        if (isSat) {
//                            newCore.add(i);
//                        }
//                    }
//
//                }
//            } else {
//                newCore = e;
//            }
//            this.refine(Not(And(newCore)));
//            return true;
//        } else {
//            return false;
//        }
//    }

    public ArrayList<Expr<BoolType>> getExprs() {
        return exprs;
    }

    public Collection<Expr<BoolType>> check(Expr<BoolType> prop) {
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(prop, 0));
            for (Expr<BoolType> ex : exprs) {
                solver.track(PathUtils.unfold(ex, 0));
            }
            SolverStatus status = solver.check();

            if (status.isSat()) {
                final Valuation model = solver.getModel();
                final MutableValuation filteredModel = new MutableValuation();
                monolithicExpr.vars().stream().map(varDecl -> varDecl.getConstDecl(0)).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                monolithicExpr.vars().stream().map(varDecl -> varDecl.getConstDecl(monolithicExpr.offsetIndex().get(varDecl))).filter(model.toMap()::containsKey).forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
                return getConjuncts(PathUtils.foldin(filteredModel.toExpr(), 0));
            } else {
                return null;
            }
        }
    }

    public boolean equalsParent() {
        if (this.parent.parent == null) {
            return false;
        }
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(Not(And(parent.getExprs())), 0));
            solver.track(PathUtils.unfold(And(exprs), 0));
            return solver.check().isUnsat();
        }
    }
}
