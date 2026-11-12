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
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Lt;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.Solver;
import java.util.Map;
import org.junit.jupiter.api.Test;
import org.kframework.mpfr.BigFloat;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

/** MathSAT is not loaded here: its native library crashes the CI test JVM. */
public class JavaSMTFpSortTest {

    @Test
    public void testFpVariableAgainstLiteral() throws Exception {
        final FpType type = FpType(8, 24);
        final ConstDecl<FpType> x = Const("x", type);
        final var zero = FpUtils.bigFloatToFpLitExpr(BigFloat.zero(type.getSignificand()), type);
        try (final Solver solver =
                JavaSMTSolverFactory.create(Solvers.Z3, new String[] {}).createSolver()) {
            solver.add(Lt(x.getRef(), zero));
            assertTrue(solver.check().isSat());
        }
    }

    @Test
    public void testMathsatInterpolatesWithProofProducingFpSolver() {
        assertEquals(
                Map.of("solver.mathsat5.furtherOptions", "theory.fp.mode=2"),
                JavaSMTSolverManager.interpolationOptions(Solvers.MATHSAT5));
        assertEquals(Map.of(), JavaSMTSolverManager.interpolationOptions(Solvers.Z3));
    }
}
