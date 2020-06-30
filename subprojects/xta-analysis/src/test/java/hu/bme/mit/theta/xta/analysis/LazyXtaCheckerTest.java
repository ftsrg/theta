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
import static hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy.LU;
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
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.DataStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaCheckerFactory;
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

	private static final Collection<String> MODELS_WITH_UNKNOWN_SOLVER_STATUS = ImmutableSet.of(MODEL_FDDI,
			MODEL_ENGINE);

	@Parameter(0)
	public String filepath;

	@Parameter(1)
	public DataStrategy dataStrategy;

	@Parameter(2)
	public ClockStrategy clockStrategy;

	private SafetyChecker<? extends XtaState<?>, XtaAction, UnitPrec> checker;

	@Parameters(name = "model: {0}, discrete: {1}, clock: {2}")
	public static Collection<Object[]> data() {
		final Collection<Object[]> result = new ArrayList<>();
		for (final String model : MODELS) {
			for (final DataStrategy dataStrategy : DataStrategy.values()) {
				for (final ClockStrategy clockStrategy : ClockStrategy.values()) {
					if (!MODELS_WITH_UNKNOWN_SOLVER_STATUS.contains(model) || (clockStrategy != LU)) {
						result.add(new Object[]{model, dataStrategy, clockStrategy});
					}
				}
			}
		}
		return result;
	}

	@Before
	public void initialize() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		final XtaSystem system = XtaDslManager.createSystem(inputStream);
		checker = LazyXtaCheckerFactory.create(system, dataStrategy, clockStrategy, BFS);
	}

	@Test
	public void test() {
		// Act
		final SafetyResult<? extends XtaState<?>, XtaAction> status = checker.check(UnitPrec.getInstance());

		// Assert
		final ArgChecker argChecker = ArgChecker.create(Z3SolverFactory.getInstance().createSolver());
		final boolean argCheckResult = argChecker.isWellLabeled(status.getArg());
		assertTrue(argCheckResult);
	}

}
