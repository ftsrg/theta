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
package hu.bme.mit.theta.cfa.analysis.impact;

import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgChecker;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLbeLts;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import org.junit.jupiter.api.Test;

public final class CfaPredImpactCheckerTest {

    @Test
    public void test() throws FileNotFoundException, IOException {
        // Arrange
        final CFA cfa =
                CfaDslManager.createCfa(
                        new FileInputStream("src/test/resources/counter5_true.cfa"));

        final Solver abstractionSolver = Z3LegacySolverFactory.getInstance().createSolver();
        final ItpSolver refinementSolver = Z3LegacySolverFactory.getInstance().createItpSolver();

        final PredImpactChecker checker =
                PredImpactChecker.create(
                        CfaLbeLts.of(cfa.getErrorLoc().get()),
                        cfa.getInitLoc(),
                        l -> l.equals(cfa.getErrorLoc().get()),
                        abstractionSolver,
                        refinementSolver);

        // Act
        final SafetyResult<
                        ARG<CfaState<PredState>, CfaAction>, Trace<CfaState<PredState>, CfaAction>>
                status = checker.check(UnitPrec.getInstance());

        // Assert
        assertTrue(status.isSafe());

        final ARG<? extends ExprState, ? extends ExprAction> arg = status.getProof();
        arg.minimize();

        final ArgChecker argChecker = ArgChecker.create(abstractionSolver);
        assertTrue(argChecker.isWellLabeled(arg));

        System.out.println(
                GraphvizWriter.getInstance()
                        .writeString(ArgVisualizer.getDefault().visualize(arg)));
    }
}
