package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.sts.STS;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class Ic3Checker {
    private final STS sts;
    private final SolverFactory solverFactory;
    private final List<Solver> F;

    public Ic3Checker(STS sts, SolverFactory solverFactory) {
        this.sts = sts;
        this.solverFactory = solverFactory;
        F = new ArrayList<Solver>();
    }

    boolean check(){

        F.add(0,Z3SolverFactory.getInstance().createSolver());
        Solver solver = F.get(0);

        solver.add(PathUtils.unfold(sts.getInit(),0));

        try (var wpp = new WithPushPop(solver)){
            solver.add(PathUtils.unfold(Not(sts.getProp()),0));
            if(solver.check().isSat()){
                return false;
            }
        }
        Integer n=0;
        n++;
        solver=Z3SolverFactory.getInstance().createSolver();
        F.add(n,solver);
        while (true) {
            solver=F.get(n);
            try (var wpp = new WithPushPop(solver)){
                solver.add(PathUtils.unfold(Not(sts.getProp()),n));
                if(solver.check().isSat()){
                    var b = F.get(n).getModel().toExpr();
                    if(!tryblock(b,n)){
                        return false;
                    }else{
                        if(n>20){
                            return true;
                        }else{
                            n++;
                            solver=Z3SolverFactory.getInstance().createSolver();
                            F.add(n,solver);
                            solver.add(PathUtils.unfold(Not(sts.getProp()),n));
                        }
                    }
                }
            }
        }
    }
    private boolean tryblock(Expr<BoolType> b,int n){
        if(n<=0){
            return false;
        }
        Solver solver = F.get(n-1);
        try (var wpp = new WithPushPop(solver)){
            solver.add(PathUtils.unfold(b, n));
            if(solver.check().isSat()){
                if(tryblock(solver.getModel().toExpr(),n-1)){
                    F.get(n).add(Not(b));
                    return true;
                }else{
                    return false;
                }
            }else{
                F.get(n).add(Not(b));
                return true;
            }
        }
    }
}
