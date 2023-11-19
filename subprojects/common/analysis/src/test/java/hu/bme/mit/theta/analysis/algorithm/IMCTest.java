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
package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.algorithm.imc.ImcChecker;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.List;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;

class IMCTest {
    @Test
    void testIMCFalse() {
        var x = Var("x", Int());
        var checker = new ImcChecker<ExprStateStub, ExprActionStub>(
                new MonolithicTransFuncStub(
                        Assign(x, Add(x.getRef(), Int(1))),
                        Eq(x.getRef(), Int(0)),
                        Neq(x.getRef(), Int(5))
                ),
                Integer.MAX_VALUE,
                Z3SolverFactory.getInstance().createItpSolver(),
                valuation -> new ExprStateStub(valuation.toExpr()),
                (valuation, valuation2) -> new ExprActionStub(List.of(Assume(valuation.toExpr()), Assume(valuation2.toExpr()))),
                List.of(x),
                0
        );

        var result = checker.check(null);
        Assertions.assertTrue(result.isUnsafe());
    }

    @Test
    void testIMCTrue() {
        var x = Var("x", Int());
        var checker = new ImcChecker<ExprStateStub, ExprActionStub>(
                new MonolithicTransFuncStub(
                        Assign(x, Mul(x.getRef(), Int(2))),
                        Eq(x.getRef(), Int(0)),
                        Neq(x.getRef(), Int(5))
                ),
                Integer.MAX_VALUE,
                Z3SolverFactory.getInstance().createItpSolver(),
                valuation -> new ExprStateStub(valuation.toExpr()),
                (valuation, valuation2) -> new ExprActionStub(List.of(Assume(valuation.toExpr()), Assume(valuation2.toExpr()))),
                List.of(x),
                0
        );

        var result = checker.check(null);
        Assertions.assertTrue(result.isSafe());
    }


}
