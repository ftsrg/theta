package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;
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

    private final List<Frame> frames;

    public Ic3Checker(STS sts, SolverFactory solverFactory) {
        this.sts = sts;
        this.solverFactory = solverFactory;
        F = new ArrayList<Solver>();
        frames=new ArrayList<>();
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

        Frame root = new Frame(null,solver);
        root.add(sts.getInit());

        int n=1;
        solver=Z3SolverFactory.getInstance().createSolver();
        F.add(n,solver);
        while (true) {
            solver=F.get(n);
            Expr<BoolType> b = null;
            try (var wpp = new WithPushPop(solver)){
                solver.add(PathUtils.unfold(Not(sts.getProp()),n));
                if(solver.check().isSat()){
                    b = F.get(n).getModel().toExpr();
                }
            }

            if (b != null) {
                if(!tryblock(b,n)){
                    return false;
                }else{
                    if(n>20){
                        return true;
                    }
                }
            }else{
                n++;
                solver=Z3SolverFactory.getInstance().createSolver();
                F.add(n,solver);
            }

        }
    }
    private boolean tryblock(Expr<BoolType> b,int n){
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
    }
}
