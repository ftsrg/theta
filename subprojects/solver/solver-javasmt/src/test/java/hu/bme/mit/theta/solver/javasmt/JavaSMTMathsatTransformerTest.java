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
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Extract;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Gt;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import org.junit.jupiter.api.Test;
import org.kframework.mpfr.BigFloat;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

/** MathSAT-specific transformer cases that the Z3-based round-trip test does not exercise. */
public class JavaSMTMathsatTransformerTest {

    @Test
    public void testBvExtractRoundtrip() throws Exception {
        final ConstDecl<BvType> x = Const("x", BvType(8));
        final Expr<BvType> expr = Extract(x.getRef(), Int(2), Int(6));

        final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
        final var config = Configuration.fromCmdLineArguments(new String[] {});
        try (final SolverContext context =
                SolverContextFactory.createSolverContext(
                        config,
                        BasicLogManager.create(config),
                        ShutdownManager.create().getNotifier(),
                        Solvers.MATHSAT5)) {
            final var term = new JavaSMTTransformationManager(symbolTable, context).toTerm(expr);
            final var back = new JavaSMTTermTransformer(symbolTable, context).toExpr(term);
            assertEquals(expr, back);
        }
    }

    @Test
    public void testFpVariableAgainstLiteral() throws Exception {
        final FpType type = FpType(8, 24);
        final ConstDecl<FpType> x = Const("x", type);
        final var zero = FpUtils.bigFloatToFpLitExpr(BigFloat.zero(type.getSignificand()), type);

        try (final Solver solver =
                JavaSMTSolverFactory.create(Solvers.MATHSAT5, new String[] {}).createSolver()) {
            solver.add(Lt(x.getRef(), zero));
            assertTrue(solver.check().isSat());
        }
    }

    /** The default, eager FP solver gives no proofs; the manager's interpolating solver must. */
    @Test
    public void testFpInterpolation() throws Exception {
        final FpType type = FpType(8, 24);
        final ConstDecl<FpType> x = Const("x", type);
        final var zero = FpUtils.bigFloatToFpLitExpr(BigFloat.zero(type.getSignificand()), type);
        try (final ItpSolver solver =
                JavaSMTSolverManager.create()
                        .getSolverFactory("JavaSMT:MATHSAT5")
                        .createItpSolver()) {
            final ItpMarker a = solver.createMarker();
            final ItpMarker b = solver.createMarker();
            final ItpPattern pattern = solver.createBinPattern(a, b);
            solver.add(a, Lt(x.getRef(), zero));
            solver.add(b, Gt(x.getRef(), zero));
            assertTrue(solver.check().isUnsat());
            assertNotNull(solver.getInterpolant(pattern).eval(a));
        }
    }
}
