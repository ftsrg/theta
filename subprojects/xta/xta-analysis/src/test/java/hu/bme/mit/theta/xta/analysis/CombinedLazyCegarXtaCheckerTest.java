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

import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfig;
import hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaCheckerConfigFactory;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.DataStrategy;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public final class CombinedLazyCegarXtaCheckerTest {
	@Parameter(0)
	public String modelPath;

	@Parameter(1)
	public String propPath;

	@Parameter(2)
	public DataStrategy dataStrategy;

	@Parameter(3)
	public ClockStrategy clockStrategy;

	@Parameter(4)
	public Boolean safety;

	private CombinedLazyCegarXtaCheckerConfig config;

	/*@Parameters(name = "model: {0}, discrete: {1}, clock: {2}")
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
	}*/

	@Parameters(name = "model: {0}, safety: {4}")
	public static Collection<Object[]> data() {
		/*final Collection<Object[]> result = new ArrayList<>();
		for (final String model : MODELS) {
			result.add(new Object[]{model, null, null, true});
		}
		return result;*/
		return List.<Object[]>of(
			new Object[]{"/model/AndOr.xta", "/property/AndOr.prop", null, null, true},
			// Extremely long
			// new Object[]{"/model/bangOlufsen.xta", "/property/bangOlufsen.prop", null, null, true},
			new Object[]{"/model/fischer-2-32-64.xta", "/property/fischer-2-32-64.prop", null, null, true},
			new Object[]{"/model/mytest.xta", "/property/mytest.prop", null, null, true},
			new Object[]{"/model/lazy-pruning-example.xta", "/property/p-errorloc.prop", null, null, true},
			new Object[]{"/model/lazy-pruning-example-2.xta", "/property/p-errorloc.prop", null, null, true}
		);
	}

	@Before
	public void initialize() throws IOException {
		final InputStream inputStream = new SequenceInputStream(
			getClass().getResourceAsStream(modelPath),
			getClass().getResourceAsStream(propPath)
		);
		final XtaSystem system = XtaDslManager.createSystem(inputStream);
		config = CombinedLazyCegarXtaCheckerConfigFactory.create(system).build();
	}

	@Test
	public void test() {
		// Act
		final SafetyResult<? extends XtaState<?>, XtaAction> status = config.check();

		// Assert
		assertEquals(safety, status.isSafe());

		/*
		final ArgChecker argChecker = ArgChecker.create(Z3SolverFactory.getInstance().createSolver());
		final boolean argCheckResult = argChecker.isWellLabeled(status.getArg());
		assertTrue(argCheckResult);
		*/
	}

}
