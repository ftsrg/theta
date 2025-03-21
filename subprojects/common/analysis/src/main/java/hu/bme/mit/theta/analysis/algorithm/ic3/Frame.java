/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.*;

public class Frame {
    private final Frame parent;
    private final Set<Expr<BoolType>> exprs;

    private final UCSolver solver;
    private final MonolithicExpr monolithicExpr;

    Frame(final Frame parent, UCSolver solver, MonolithicExpr monolithicExpr) {
        this.parent = parent;
        this.solver = solver;
        this.monolithicExpr = monolithicExpr;
        exprs = new HashSet<>();
    }

    public void refine(Expr<BoolType> expression) {
        Collection<Expr<BoolType>> col = getConjuncts(expression);
        for (Expr<BoolType> e : col) {
            exprs.add(e);
        }
    }

    public Set<Expr<BoolType>> getExprs() {
        return exprs;
    }

    public Collection<Expr<BoolType>> check(Expr<BoolType> target) {
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(target, 0));
            for (Expr<BoolType> ex : exprs) {
                solver.track(PathUtils.unfold(ex, 0));
            }
            SolverStatus status = solver.check();

            if (status.isSat()) {
                final Valuation model = solver.getModel();
                final MutableValuation filteredModel = new MutableValuation();
                monolithicExpr.getVars().stream()
                        .map(varDecl -> varDecl.getConstDecl(0))
                        .filter(model.toMap()::containsKey)
                        .forEach(decl -> filteredModel.put(decl, model.eval(decl).get()));
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
