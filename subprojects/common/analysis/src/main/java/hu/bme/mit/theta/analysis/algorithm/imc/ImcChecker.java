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
package hu.bme.mit.theta.analysis.algorithm.imc;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;


import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;


public class ImcChecker<S extends ExprState, A extends StmtAction> implements SafetyChecker<S, A, UnitPrec> {
    final Expr<BoolType> trans;
    final Expr<BoolType> init;
    final Expr<BoolType> prop;
    final int upperBound;
    ItpSolver solver;
    final VarIndexing firstIndexing;
    final VarIndexing offset;
    final Function<Valuation, S> valToState;
    final Collection<VarDecl<?>> vars;
    final boolean interpolateForward;

    public ImcChecker(MonolithicTransFunc transFunc,
                      int upperBound,
                      ItpSolver solver,
                      Function<Valuation, S> valToState,
                      Collection<VarDecl<?>> vars,
                      boolean interpolateForward1) {
        this.trans = transFunc.getTransExpr();
        this.init = transFunc.getInitExpr();
        this.prop = transFunc.getPropExpr();
        this.upperBound = upperBound;
        this.solver = solver;
        this.firstIndexing = transFunc.getInitIndexing();
        this.offset = transFunc.getOffsetIndexing();
        this.valToState = valToState;
        this.vars = vars;
        interpolateForward = interpolateForward1;
    }


    @Override
    public SafetyResult<S, A> check(UnitPrec prec) {
        int i = 0;
        var exprsFromStart = new ArrayList<>(List.of(PathUtils.unfold(init, VarIndexingFactory.indexing(0))));
        var listOfIndexes = new ArrayList<>(List.of(firstIndexing));

        final ItpMarker a = solver.createMarker();
        final ItpMarker b = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(a, b);

        while (i < upperBound) {
            i++;
            var newIndex = listOfIndexes.get(i - 1).add(offset);
            var expression = PathUtils.unfold(trans, listOfIndexes.get(i - 1));

            exprsFromStart.add(expression);
            listOfIndexes.add(newIndex);

            var unfoldedProp = Not(PathUtils.unfold(prop, newIndex));

            solver.push();
            solver.add(a, And(exprsFromStart.subList(0, 2)));
            solver.add(b, And(And(exprsFromStart.subList(2, exprsFromStart.size())), unfoldedProp));


            var img = exprsFromStart.get(0);

            var status = solver.check();
            if (status.isSat()) {
                S initial = null;
                for (int j = 0; j < listOfIndexes.size(); j++) {
                    var valuation = PathUtils.extractValuation(solver.getModel(), listOfIndexes.get(j), vars);

                    S st = valToState.apply(valuation);
                    if (initial == null)
                        initial = st;
                }
                Trace<S, A> trace = Trace.of(List.of(initial), List.of());
                return SafetyResult.unsafe(trace, ARG.create(null));
            }
            // reached fixed point
            while (status.isUnsat()) {
                var interpolant = solver.getInterpolant(pattern);
                var itpFormula = PathUtils.unfold(PathUtils.foldin(interpolant.eval(a), listOfIndexes.get(1)), listOfIndexes.get(0));
                solver.pop();
                try (var pps = new WithPushPop(solver)) {
                    solver.add(a, And(itpFormula, Not(img)));
                    if (solver.check().isUnsat()) {
                        return SafetyResult.safe(ARG.create((state1, state2) -> false));
                    }
                }
                img = Or(img, itpFormula);

                solver.push();
                solver.add(a, And(itpFormula, exprsFromStart.get(1)));
                solver.add(b, And(And(exprsFromStart.subList(2, exprsFromStart.size())), unfoldedProp));

                status = solver.check();
            }
            solver.pop();

        }
        return null;
    }


}

