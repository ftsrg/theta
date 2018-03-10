/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis;

import static hu.bme.mit.theta.analysis.algorithm.SearchStrategy.BFS;
import static hu.bme.mit.theta.xta.analysis.lazy.Algorithm.BINITP;
import static hu.bme.mit.theta.xta.analysis.lazy.Algorithm.EXPLBINITP;
import static hu.bme.mit.theta.xta.analysis.lazy.Algorithm.EXPLLU;
import static hu.bme.mit.theta.xta.analysis.lazy.Algorithm.EXPLSEQITP;
import static hu.bme.mit.theta.xta.analysis.lazy.Algorithm.LU;
import static hu.bme.mit.theta.xta.analysis.lazy.Algorithm.SEQITP;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.lazy.Algorithm;
import hu.bme.mit.theta.xta.analysis.lazy.AlgorithmStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaChecker;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;

@RunWith(Parameterized.class)
public final class LazyXtaCheckerTest {
	private static final String MODEL_CSMA = "/csma-2.xta";
	private static final String MODEL_FDDI = "/fddi-2.xta";
	private static final String MODEL_FISCHER = "/fischer-2-32-64.xta";
	private static final String MODEL_LYNCH = "/lynch-2-16.xta";
	private static final String MODEL_ENGINE = "/engine-classic.xta";

	private static final Collection<String> MODELS = ImmutableList.of(MODEL_CSMA, MODEL_FDDI, MODEL_FISCHER,
			MODEL_LYNCH, MODEL_ENGINE);

	private static final Collection<Algorithm> ALGORITHMS = ImmutableList.of(BINITP, SEQITP, LU, EXPLBINITP, EXPLSEQITP,
			EXPLLU);

	private static final Collection<String> MODELS_WITH_UNKNOWN_SOLVER_STATUS = ImmutableSet.of(MODEL_FDDI,
			MODEL_ENGINE);

	@Parameter(0)
	public String filepath;

	@Parameter(1)
	public Algorithm algorithm;

	private XtaSystem system;
	private AlgorithmStrategy<?> algorithmStrategy;

	@Parameters(name = "model: {0}, algorithm: {1}")
	public static Collection<Object[]> data() {
		final Collection<Object[]> result = new ArrayList<>();
		for (final String model : MODELS) {
			for (final Algorithm algorithm : ALGORITHMS) {
				if (!MODELS_WITH_UNKNOWN_SOLVER_STATUS.contains(model) || (algorithm != LU && algorithm != EXPLLU)) {
					result.add(new Object[] { model, algorithm });
				}
			}
		}
		return result;
	}

	@Before
	public void initialize() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		system = XtaDslManager.createSystem(inputStream);
		algorithmStrategy = algorithm.createStrategy(system);
	}

	@Test
	public void test() {
		// Arrange
		final LazyXtaChecker<?> checker = LazyXtaChecker.create(system, algorithmStrategy, BFS);

		// Act
		final SafetyResult<? extends XtaState<?>, XtaAction> status = checker.check(UnitPrec.getInstance());

		// Assert
		final ArgChecker argChecker = ArgChecker.create(Z3SolverFactory.getInstace().createSolver());
		final boolean argCheckResult = argChecker.isWellLabeled(status.getArg());
		assertTrue(argCheckResult);
	}

}
