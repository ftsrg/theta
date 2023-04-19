package hu.bme.mit.theta.analysis.algorithm.kind;


import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;


public class KIndChecker<S  extends ExprState, A extends ExprAction> implements SafetyChecker<S, A, UnitPrec> {
    final Expr<BoolType> trans;
    final Expr<BoolType> init;
    final Expr<BoolType> prop;
    final int upperBound;
    Solver solver;
    final VarIndexing firstIndexing;

    public KIndChecker(Expr<BoolType> trans,
                       Expr<BoolType> init,
                       Expr<BoolType> prop,
                       int upperBound,
                       Solver solver,
                       VarIndexing firstIndexing) {
        this.trans = trans;
        this.init = init;
        this.prop = prop;
        this.upperBound = upperBound;
        this.solver = solver;
        this.firstIndexing = firstIndexing;

    }



    @Override
    public SafetyResult<S, A> check(UnitPrec prec) {
        int i=0;

        //induktivitás index VarIndexingFactory.indexing(0) -ról indul
        //expFromStart index pedig init index-ről
        //

        var exprsFromStart=new ArrayList<Expr<BoolType>>();
        var exprsForInductivity=new ArrayList<Expr<BoolType>>();

        exprsFromStart.add(PathUtils.unfold(init,VarIndexingFactory.indexing(0))); // VarIndexingFactory.indexing(0)?
        exprsFromStart.add(PathUtils.unfold(trans,firstIndexing.add(VarIndexingFactory.indexing(i))));// init index?

        exprsForInductivity.add(PathUtils.unfold(trans,VarIndexingFactory.indexing(i)));
        exprsForInductivity.add(prop);

        while(i<upperBound){
            if (i > 0) {
                exprsFromStart.add(PathUtils.unfold(trans,firstIndexing.add(VarIndexingFactory.indexing(i))));

                exprsForInductivity.add(ExprUtils.applyPrimes(prop,VarIndexingFactory.indexing(i)));
                exprsForInductivity.add(PathUtils.unfold(trans,firstIndexing.add(VarIndexingFactory.indexing(i))));
            }
            // Checking loop free path of length i *kesobb*
            /*try (var s = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(And(exprsFromStart), 0));
                //solver.add(varExpr);

                if(solver.check().isUnsat()){
                    var x=0;
                    return //safe;
                }
            }*/
            // Counterexample feasibility check
            try (var s = new WithPushPop(solver)) {
                // I1 and T1-2 and T2-3 and ... and Tk-1-k
                solver.add(And(exprsFromStart));
                // Not Pk
                solver.add(PathUtils.unfold(Not(prop), firstIndexing.add(VarIndexingFactory.indexing(i))));

                if (solver.check().isSat()) {
                    //trace kesobb

                    return SafetyResult.Unsafe.unsafe(trace,arg); //??
                }
            }

            // Property k-inductivity check
            try (var s = new WithPushPop(solver)) {
                // P1 and T1-2 and P2 and ... and Tk-k+1
                solver.add(PathUtils.unfold(And(exprsForInductivity), VarIndexingFactory.indexing(0)));
                // Not Pk+1
                solver.add(PathUtils.unfold(Not(prop),VarIndexingFactory.indexing(i+1))); //index?

                if (solver.check().isUnsat()) {
                    return SafetyResult.Safe.safe(arg); //??
                }
            }
            i++;
        }
        return null;
    }


}
