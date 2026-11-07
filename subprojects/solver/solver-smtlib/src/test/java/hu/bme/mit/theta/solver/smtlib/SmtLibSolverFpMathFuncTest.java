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
package hu.bme.mit.theta.solver.smtlib;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.MathFunc;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr;
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr.Function;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.testing.SolverInstallations;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class SmtLibSolverFpMathFuncTest {

    private static final FpType FLOAT = FpType.of(8, 24);
    private static final FpType DOUBLE = FpType.of(11, 53);
    private static SolverFactory solverFactory;

    @BeforeAll
    public static void init() {
        solverFactory = SolverInstallations.installOrSkip("cvc5", "1.3.4");
    }

    private static SolverStatus check(final Expr<BoolType> e) throws Exception {
        try (Solver solver = solverFactory.createSolver()) {
            solver.add(e);
            return solver.check();
        }
    }

    @Test
    public void equalArgumentsGiveEqualResults() throws Exception {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final ConstDecl<FpType> y = Const("y", FLOAT);
        final var differ =
                Not(
                        FpAssign(
                                MathFunc(Function.EXP, x.getRef()),
                                MathFunc(Function.EXP, y.getRef())));
        assertEquals(SolverStatus.UNSAT, check(And(FpAssign(x.getRef(), y.getRef()), differ)));
    }

    @Test
    public void resultIsUninterpreted() throws Exception {
        final var one = FpUtils.fromString("1.0", FLOAT);
        final var hundred = FpUtils.fromString("100.0", FLOAT);
        assertEquals(SolverStatus.SAT, check(FpAssign(MathFunc(Function.EXP, one), hundred)));
    }

    /** One name may not carry two signatures in SMT-LIB: each sort gets its own declaration. */
    @Test
    public void twoSortsInOneQuery() throws Exception {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final ConstDecl<FpType> d = Const("d", DOUBLE);
        final var both =
                And(
                        FpAssign(MathFunc(Function.SIN, x.getRef()), x.getRef()),
                        FpAssign(MathFunc(Function.SIN, d.getRef()), d.getRef()));
        assertEquals(SolverStatus.SAT, check(both));
    }

    @Test
    public void declarationFollowsPushPop() throws Exception {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final var fact = FpAssign(MathFunc(Function.LOG, x.getRef()), x.getRef());
        try (Solver solver = solverFactory.createSolver()) {
            solver.push();
            solver.add(fact);
            assertEquals(SolverStatus.SAT, solver.check());
            solver.pop();
            solver.push();
            solver.add(fact);
            assertEquals(SolverStatus.SAT, solver.check());
            solver.pop();
        }
    }

    @Test
    public void interpolantMentionsTheFunction() throws Exception {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final ConstDecl<FpType> y = Const("y", FLOAT);
        final ConstDecl<FpType> r = Const("r", FLOAT);
        try (ItpSolver solver = solverFactory.createItpSolver()) {
            final ItpMarker a = solver.createMarker();
            final ItpMarker b = solver.createMarker();
            solver.add(a, FpAssign(r.getRef(), MathFunc(Function.EXP, x.getRef())));
            solver.add(b, FpAssign(x.getRef(), y.getRef()));
            solver.add(b, Not(FpAssign(r.getRef(), MathFunc(Function.EXP, y.getRef()))));
            assertEquals(SolverStatus.UNSAT, solver.check());
            final var itp = solver.getInterpolant(solver.createBinPattern(a, b)).eval(a);
            assertTrue(contains(itp), "interpolant without the function: " + itp);
        }
    }

    private static boolean contains(final Expr<?> e) {
        return e instanceof FpMathFuncExpr
                || e.getOps().stream().anyMatch(SmtLibSolverFpMathFuncTest::contains);
    }
}
