/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.ic3;

import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.*;

public class UnderFrame {
    private final Set<Expr<BoolType>> exprs;

    public List<Expr<BoolType>> getExprsinList() {
        return exprsinList;
    }

    private final List<Expr<BoolType>> exprsinList;

    public List<Integer> getParents() {
        return parents;
    }

    private final List<Integer> parents;
    private final UCSolver solver;

    public UnderFrame(UCSolver solver) {
        this.solver = solver;
        exprs = new HashSet<>();
        parents = new ArrayList<>();
        exprsinList = new ArrayList<>();
    }

    public int expand(Expr<BoolType> expression, int parent) {
        int size = exprs.size();
        exprs.add(expression); // todo can be broken by OR
        if (exprs.size() > size) {
            exprsinList.add(expression);
            parents.add(parent);
        }
        return exprsinList.indexOf(expression);
    }

    public Set<Expr<BoolType>> getExprs() {
        return exprs;
    }

    public Collection<Expr<BoolType>> check(Expr<BoolType> start) {
        for (var ex : exprs) { // todo needs to be more efficient maybe with OR?
            try (var wpp = new WithPushPop(solver)) {
                solver.track(PathUtils.unfold(start, 0));
                solver.track(PathUtils.unfold(ex, 0));
                SolverStatus status = solver.check();
                if (status.isSat()) {
                    final Valuation model = solver.getModel();
                    final MutableValuation filteredModel = new MutableValuation();
                    /*monolithicExpr.getVars().stream()
                    .map(varDecl -> varDecl.getConstDecl(0))
                    .filter(model.toMap()::containsKey)
                    .forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));*/
                    return getConjuncts(PathUtils.foldin(filteredModel.toExpr(), 0));
                }
            }
        }
        return null;
    }
}
