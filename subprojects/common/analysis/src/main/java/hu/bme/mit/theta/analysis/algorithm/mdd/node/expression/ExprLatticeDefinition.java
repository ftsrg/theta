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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ExprLatticeDefinition {

    public static LatticeDefinition<Expr> forExpr() {
        return new LatticeDefinition<>(
                Expr.class,
                False(),
                True(),
                SmartBoolExprs::Or,
                SmartBoolExprs::And,
                (a, b) -> And(a, Not(b)));
    }

    /**
     * Terminals hold a formula over the token values: an unsatisfiable intersection is bottom, and
     * a union returns an operand that implies the other, so fixpoints are detected. Names bound in
     * both operands of an intersection stand for different values.
     */
    @SuppressWarnings("unchecked")
    public static LatticeDefinition<Expr> forSymbolicExpr(SolverPool solverPool) {
        final Map<Expr<BoolType>, Boolean> satCache = new HashMap<>();
        final Map<List<Expr<BoolType>>, Expr<BoolType>> unions = new HashMap<>();
        final var lattice =
                new Object() {
                    boolean isSat(Expr<BoolType> expr) {
                        final Expr<BoolType> simplified = ExprUtils.simplify(expr);
                        if (simplified instanceof TrueExpr) return true;
                        if (simplified instanceof FalseExpr) return false;
                        final Boolean cached = satCache.get(simplified);
                        if (cached != null) return cached;
                        final var solver = solverPool.requestSolver();
                        final boolean sat;
                        try (var wpp = new WithPushPop(solver)) {
                            solver.add(simplified);
                            sat = solver.check().isSat();
                        } finally {
                            solverPool.returnSolver(solver);
                        }
                        satCache.put(simplified, sat);
                        return sat;
                    }

                    Expr<BoolType> feasible(Expr<BoolType> expr) {
                        final Expr<BoolType> simplified = ExprUtils.simplify(expr);
                        return isSat(simplified) ? simplified : False();
                    }

                    Expr<BoolType> union(Expr<BoolType> a, Expr<BoolType> b) {
                        if (a.equals(b) || b instanceof FalseExpr || a instanceof TrueExpr)
                            return a;
                        if (a instanceof FalseExpr || b instanceof TrueExpr) return b;
                        if (!isSat(And(b, Not(a)))) return a;
                        if (!isSat(And(a, Not(b)))) return b;
                        return SmartBoolExprs.Or(a, b);
                    }
                };
        return new LatticeDefinition<>(
                Expr.class,
                False(),
                True(),
                (a, b) -> unions.computeIfAbsent(List.of(a, b), k -> lattice.union(a, b)),
                (a, b) -> lattice.feasible(And(a, SymbolicKeys.renamedApart(a, b))),
                (a, b) -> lattice.feasible(And(a, Not(b))));
    }
}
