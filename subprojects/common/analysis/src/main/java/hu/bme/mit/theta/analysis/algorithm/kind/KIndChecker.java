package hu.bme.mit.theta.analysis.algorithm.kind;


import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;


public class KIndChecker<S  extends ExprState, A extends ExprAction> implements SafetyChecker<S, A, UnitPrec> {
    final Expr<BoolType> trans;
    final Expr<BoolType> init;
    final Expr<BoolType> prop;
    final int upperBound;
    Solver solver;
    final VarIndexing firstIndexing;
    final VarIndexing offset;
    final Function<Valuation, S> valToState;
    final Collection<VarDecl<?>> vars;


    public KIndChecker(MonolithicTransFunc transFunc,
                       int upperBound,
                       Solver solver,
                       Function<Valuation,S> valToState,
                       Collection<VarDecl<?>> vars) {
        this.trans = transFunc.getTransExpr();
        this.init = transFunc.getInitExpr();
        this.prop = transFunc.getPropExpr();
        this.upperBound = upperBound;
        this.solver = solver;
        this.firstIndexing = transFunc.getInitIndexing();
        this.offset = transFunc.getOffsetIndexing();
        this.valToState = valToState;
        this.vars = vars;
    }



    @Override
    public SafetyResult<S, A> check(UnitPrec prec) {
        //var trans = action.toExpr();
        //var offset = action.nextIndexing();

        int i=0;
        var currIndex = firstIndexing;


        var exprsFromStart=new ArrayList<Expr<BoolType>>();
        var exprsForInductivity=new ArrayList<Expr<BoolType>>();
        var listOfIndexes = new ArrayList<VarIndexing>();

        exprsFromStart.add(PathUtils.unfold(init,VarIndexingFactory.indexing(0))); // VarIndexingFactory.indexing(0)?
        var eqList= new ArrayList<Expr<BoolType>>();
        while(i<upperBound){


                exprsFromStart.add(PathUtils.unfold(trans,currIndex));

                // külső lista üres
                var finalList= new ArrayList<Expr<BoolType>>();

                for(int j = 0; j < listOfIndexes.size(); j++) {
                    // új belső lista az adott indexű állapothoz
                    var tempList = new ArrayList<Expr<BoolType>>();
                    for (var v : vars) {
                        // a mostani listához adom az Eq-et
                        tempList.add(Eq(PathUtils.unfold(v.getRef(),currIndex), PathUtils.unfold(v.getRef(), listOfIndexes.get(j))));
                    }
                     finalList.add(Not(And(tempList)));
                }
                eqList.addAll(finalList);
                listOfIndexes.add(currIndex);


                exprsForInductivity.add(PathUtils.unfold(prop,currIndex.sub(firstIndexing))); //0-ról indítva
                exprsForInductivity.add(PathUtils.unfold(trans,currIndex.sub(firstIndexing)));

                currIndex=currIndex.add(offset);

            // Checking loop free path of length i
            try (var s = new WithPushPop(solver)) {
                solver.add(And(exprsFromStart));
                solver.add(eqList);

                if(solver.check().isUnsat()){
                    var x=0;
                    return SafetyResult.safe(ARG.create(null));
                }
            }
            // Counterexample feasibility check
            try (var s = new WithPushPop(solver)) {
                // I1 and T1-2 and T2-3 and ... and Tk-1-k
                solver.add(And(exprsFromStart));
                // Not Pk
                solver.add(PathUtils.unfold(Not(prop),currIndex));

                if (solver.check().isSat()) {
                    S initial = null;
                    for (int j = 0; j < listOfIndexes.size(); j++) {
                        var valuation = PathUtils.extractValuation(solver.getModel(), listOfIndexes.get(j), vars);

                        S st = valToState.apply(valuation);
                        if(initial == null)
                            initial = st;
                    }
                    Trace<S, A> trace = Trace.of(List.of(initial), List.of());
                    return SafetyResult.unsafe(trace,ARG.create(null));
                }
            }

            // Property k-inductivity check
            try (var s = new WithPushPop(solver)) {
                // P1 and T1-2 and P2 and ... and Tk-k+1
                solver.add(And(exprsForInductivity));
                // Not Pk+1
                solver.add(PathUtils.unfold(Not(prop),currIndex.sub(firstIndexing)));

                if (solver.check().isUnsat()) {
                    return SafetyResult.safe(ARG.create(null));
                }
            }
            i++;
        }
        return null;
    }


}
