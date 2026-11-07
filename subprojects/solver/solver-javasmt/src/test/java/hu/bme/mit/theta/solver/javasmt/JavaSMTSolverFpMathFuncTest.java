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
package hu.bme.mit.theta.solver.javasmt;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.MathFunc;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr.Function;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

public class JavaSMTSolverFpMathFuncTest {

    private static final FpType FLOAT = FpType.of(8, 24);
    private static final FpType DOUBLE = FpType.of(11, 53);

    private static SolverStatus check(final Solvers backend, final Expr<BoolType> e)
            throws Exception {
        try (Solver solver = JavaSMTSolverFactory.create(backend, new String[] {}).createSolver()) {
            solver.add(e);
            return solver.check();
        }
    }

    @ParameterizedTest
    @EnumSource(
            value = Solvers.class,
            names = {"Z3", "CVC5"})
    public void equalArgumentsGiveEqualResults(final Solvers backend) throws Exception {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final ConstDecl<FpType> y = Const("y", FLOAT);
        final var differ =
                Not(
                        FpAssign(
                                MathFunc(Function.EXP, x.getRef()),
                                MathFunc(Function.EXP, y.getRef())));
        assertEquals(
                SolverStatus.UNSAT, check(backend, And(FpAssign(x.getRef(), y.getRef()), differ)));
    }

    @ParameterizedTest
    @EnumSource(
            value = Solvers.class,
            names = {"Z3", "CVC5"})
    public void resultIsUninterpretedPerSort(final Solvers backend) throws Exception {
        final var hundred = FpUtils.fromString("100.0", FLOAT);
        final ConstDecl<FpType> d = Const("d", DOUBLE);
        final var e =
                And(
                        FpAssign(MathFunc(Function.EXP, FpUtils.fromString("1.0", FLOAT)), hundred),
                        FpAssign(MathFunc(Function.EXP, d.getRef()), d.getRef()));
        assertEquals(SolverStatus.SAT, check(backend, e));
    }

    @ParameterizedTest
    @EnumSource(
            value = Solvers.class,
            names = {"Z3"})
    public void termRoundTrip(final Solvers backend) throws Exception {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final var config = Configuration.fromCmdLineArguments(new String[] {});
        try (final SolverContext context =
                SolverContextFactory.createSolverContext(
                        config,
                        BasicLogManager.create(config),
                        ShutdownManager.create().getNotifier(),
                        backend)) {
            final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
            final var manager = new JavaSMTTransformationManager(symbolTable, context);
            final var termTransformer = new JavaSMTTermTransformer(symbolTable, context);
            for (final Function f : Function.values()) {
                final var expr = MathFunc(f, x.getRef());
                assertEquals(expr, termTransformer.toExpr(manager.toTerm(expr)));
            }
        }
    }
}
