/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.analysis.algorithm.kind;


import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;


public class KIndChecker<S extends ExprState, A extends ExprAction> implements SafetyChecker<S, A, UnitPrec> {
    private final Expr<BoolType> trans;
    private final Expr<BoolType> init;
    private final Expr<BoolType> prop;
    private final int upperBound;
    private final int inductionStartBound;
    private final int inductionFrequency;
    private final Solver solver1;
    private final Solver solver2;
    private final VarIndexing firstIndexing;
    private final VarIndexing offset;
    private final Function<Valuation, S> valToState;
    private final BiFunction<Valuation, Valuation, A> valsToAction;
    private final Collection<VarDecl<?>> vars;


    public KIndChecker(MonolithicTransFunc transFunc,
                       int upperBound,
                       int inductionStartBound,
                       int inductionFrequency,
                       Solver solver1,
                       Solver solver2,
                       Function<Valuation, S> valToState,
                       BiFunction<Valuation, Valuation, A> valsToAction,
                       Collection<VarDecl<?>> vars) {
        this.trans = transFunc.getTransExpr();
        this.init = transFunc.getInitExpr();
        this.prop = transFunc.getPropExpr();
        this.upperBound = upperBound;
        this.inductionStartBound = inductionStartBound;
        this.inductionFrequency = inductionFrequency;
        this.solver1 = solver1;
        this.solver2 = solver2;
        this.firstIndexing = transFunc.getInitIndexing();
        this.offset = transFunc.getOffsetIndexing();
        this.valToState = valToState;
        this.valsToAction = valsToAction;
        this.vars = vars;
    }


    @Override
    public SafetyResult<S, A> check(UnitPrec prec) {
        int i = 0;
        var currIndex = firstIndexing;


        var listOfIndexes = new ArrayList<VarIndexing>();

        solver1.add(PathUtils.unfold(init, VarIndexingFactory.indexing(0)));
        var eqList = new ArrayList<Expr<BoolType>>();
        while (i < upperBound) {
            // BMC part

            solver1.add(PathUtils.unfold(trans, currIndex));

            var finalList = new ArrayList<Expr<BoolType>>();

            for (int j = 0; j < listOfIndexes.size(); j++) {
                var tempList = new ArrayList<Expr<BoolType>>();
                for (var v : vars) {
                    tempList.add(Eq(PathUtils.unfold(v.getRef(), currIndex), PathUtils.unfold(v.getRef(), listOfIndexes.get(j))));
                }
                finalList.add(Not(And(tempList)));
            }
            eqList.addAll(finalList);
            listOfIndexes.add(currIndex);

            var lastIndex = currIndex;

            currIndex = currIndex.add(offset);

            // Checking loop free path of length i

            solver1.push();
            solver1.add(eqList);

            if (solver1.check().isUnsat()) {

                return SafetyResult.safe(ARG.create(null));
            }
            solver1.pop();

            // Counterexample feasibility check

            // I1 and T1-2 and T2-3 and ... and Tk-1-k

            // Not Pk
            solver1.push();
            solver1.add(PathUtils.unfold(Not(prop), currIndex));

            if (solver1.check().isSat()) {
                // otherwise trace is cut off before last action
                listOfIndexes.add(currIndex);
                var stateList = new LinkedList<S>();
                var actionList = new LinkedList<A>();
                if (valToState != null && valsToAction != null) {
                    Valuation lastValuation = null;
                    for (int j = 0; j < listOfIndexes.size(); j++) {
                        VarIndexing listOfIndex = listOfIndexes.get(j);
                        var valuation = PathUtils.extractValuation(solver1.getModel(), listOfIndex, vars);
                        stateList.add(valToState.apply(valuation));
                        if (j > 0) {
                            actionList.add(valsToAction.apply(lastValuation, valuation));
                        }
                        lastValuation = valuation;
                    }
                }
                Trace<S, A> trace = Trace.of(stateList, actionList);
                return SafetyResult.unsafe(trace, ARG.create(null));
            }
            solver1.pop();

            // KIND part

            // P1 and T1-2 and P2 and ... and Tk-k+1

            solver2.add(PathUtils.unfold(prop, lastIndex.sub(firstIndexing)));
            solver2.add(PathUtils.unfold(trans, lastIndex.sub(firstIndexing)));

            // Not Pk+1
            if (i >= inductionStartBound && (i - inductionStartBound) % inductionFrequency == 0) {
                solver2.push();
                solver2.add(PathUtils.unfold(Not(prop), currIndex.sub(firstIndexing)));

                if (solver2.check().isUnsat()) {
                    return SafetyResult.safe(ARG.create(null));
                }
                solver2.pop();
            }
            i++;
        }
        return null;
    }


}
