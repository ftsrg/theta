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
package hu.bme.mit.theta.solver.smtlib;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.AllSatSolver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.testing.SolverInstallations;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * {@code check-allsat} through the real MathSAT binary. The interesting case is a *sequence* of
 * all-sat calls on one long-lived solver, because each call returns many parenthesised responses in
 * a row -- the shape that used to be mis-framed by the response reader.
 */
public final class AllSatProbeTest {
    private static SolverFactory solverFactory;

    private static final String SOLVER = "mathsat";
    private static final String VERSION = "5.6.12";

    @BeforeAll
    public static void init() {
        solverFactory = SolverInstallations.installOrSkip(SOLVER, VERSION);
    }

    @BeforeEach
    public void before() {
        Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX));
    }

    /**
     * {@code lit_i <-> x >= i} for i in 0..3 is a chain: a model is fixed by how many of the
     * thresholds x clears, so there are exactly 5 cubes and every one assigns all 4 literals.
     * Repeated three times on the same solver process, which is how {@code BooleanAbstractor} uses
     * it.
     */
    @Test
    public void repeatedAllSatOnOneSolver() {
        final var solver = solverFactory.createSolver();
        assertTrue(solver instanceof AllSatSolver s && s.supportsAllSat());

        final var x = Const("x", Int());
        final int nPreds = 4;
        final List<ConstDecl<BoolType>> lits = new ArrayList<>();
        for (int i = 0; i < nPreds; i++) {
            lits.add(Const("__actlit_" + i, Bool()));
        }

        for (int r = 0; r < 3; r++) {
            final int round = r;
            solver.push();
            for (int i = 0; i < nPreds; i++) {
                solver.add(Iff(lits.get(i).getRef(), Geq(x.getRef(), Int(i))));
            }
            solver.push();
            final var models = ((AllSatSolver) solver).allSat(lits);
            solver.pop();
            solver.pop();

            assertEquals(nPreds + 1, models.size(), "cube count, round " + round);
            assertEquals(
                    models.size(),
                    new LinkedHashSet<>(models).size(),
                    "cubes must not repeat, round " + round);
            models.forEach(
                    m ->
                            assertEquals(
                                    nPreds,
                                    m.getDecls().size(),
                                    "every cube must be total, round " + round));
        }
    }
}
