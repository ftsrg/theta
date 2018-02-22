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
package hu.bme.mit.theta.formalism.xta.analysis;

import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.BinItpStrategy;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.ItpStrategy.ItpOperator;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.LazyXtaChecker;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.LuStrategy;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.SeqItpStrategy;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;

@RunWith(Parameterized.class)
public final class LazyXtaCheckerTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/csma-2.xta" },

				{ "/fddi-2.xta" },

				{ "/fischer-2-32-64.xta" },

				{ "/lynch-2-16.xta" }

		});
	}

	@Parameter(0)
	public String filepath;

	private XtaSystem system;

	@Before
	public void initialize() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		system = XtaDslManager.createSystem(inputStream);
	}

	@Test
	public void testBinItpStrategy() {
		// Arrange
		final LazyXtaChecker<?> checker = LazyXtaChecker.create(system,
				BinItpStrategy.create(system, ItpOperator.DEFAULT), SearchStrategy.BFS);

		// Act
		final SafetyResult<?, XtaAction> status = checker.check(UnitPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());
		System.out.println(status.getStats().get());
	}

	@Test
	public void testSeqItpStrategy() {
		// Arrange
		final LazyXtaChecker<?> checker = LazyXtaChecker.create(system,
				SeqItpStrategy.create(system, ItpOperator.DEFAULT), SearchStrategy.BFS);

		// Act
		final SafetyResult<?, XtaAction> status = checker.check(UnitPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());
		System.out.println(status.getStats().get());
	}

	@Test
	public void testLuStrategy() {
		// Arrange
		final LazyXtaChecker<?> checker = LazyXtaChecker.create(system, LuStrategy.create(system), SearchStrategy.BFS);

		// Act
		final SafetyResult<?, XtaAction> status = checker.check(UnitPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());
		System.out.println(status.getStats().get());
	}

}
