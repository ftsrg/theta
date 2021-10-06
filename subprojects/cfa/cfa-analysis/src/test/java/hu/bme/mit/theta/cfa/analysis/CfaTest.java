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
package hu.bme.mit.theta.cfa.analysis;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileInputStream;
import java.util.Arrays;
import java.util.Collection;

import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.EXPL;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.PRED_BOOL;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.PRED_CART;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.BW_BIN_ITP;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.NWT_IT_WP;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.SEQ_ITP;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.UCB;

@RunWith(value = Parameterized.class)
public class CfaTest {
	@Parameterized.Parameter(value = 0)
	public String filePath;

	@Parameterized.Parameter(value = 1)
	public CfaConfigBuilder.Domain domain;

	@Parameterized.Parameter(value = 2)
	public CfaConfigBuilder.Refinement refinement;

	@Parameterized.Parameter(value = 3)
	public boolean isSafe;

	@Parameterized.Parameter(value = 4)
	public int cexLength;

	@Parameterized.Parameter(value = 5)
	public String solver;

	@Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "src/test/resources/arithmetic-bool00.cfa", PRED_CART, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool00.cfa", PRED_BOOL, BW_BIN_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool00.cfa", EXPL, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool01.cfa", PRED_CART, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool01.cfa", PRED_BOOL, BW_BIN_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool01.cfa", EXPL, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool10.cfa", PRED_BOOL, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool10.cfa", PRED_CART, BW_BIN_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool10.cfa", EXPL, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool11.cfa", PRED_CART, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool11.cfa", PRED_BOOL, BW_BIN_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-bool11.cfa",  EXPL, SEQ_ITP, false, 15, "Z3" },

				{ "src/test/resources/arithmetic-int.cfa", PRED_CART, SEQ_ITP, false, 13, "Z3" },

				{ "src/test/resources/arithmetic-int.cfa", PRED_BOOL, BW_BIN_ITP, false, 13, "Z3" },

				{ "src/test/resources/arithmetic-int.cfa",  EXPL, SEQ_ITP, false, 13, "Z3" },

				{ "src/test/resources/arithmetic-mod.cfa",  PRED_CART, SEQ_ITP, true, 0, "Z3" },

				{ "src/test/resources/arithmetic-mod.cfa",  EXPL, BW_BIN_ITP, true, 0, "Z3" },

				{ "src/test/resources/arrays.cfa", PRED_CART, SEQ_ITP, false, 8, "Z3" },

				{ "src/test/resources/arrays.cfa", PRED_BOOL, BW_BIN_ITP, false, 8, "Z3" },

				{ "src/test/resources/arrayinit.cfa", PRED_CART, BW_BIN_ITP, false, 3, "Z3" },

				{ "src/test/resources/arrays.cfa", EXPL, SEQ_ITP, false, 8, "Z3" },

				{ "src/test/resources/counter5_true.cfa", PRED_BOOL, SEQ_ITP, true, 0, "Z3" },

				{ "src/test/resources/counter5_true.cfa", PRED_CART, BW_BIN_ITP, true, 0, "Z3" },

				{ "src/test/resources/counter5_true.cfa", EXPL, SEQ_ITP, true, 0, "Z3" },

				{ "src/test/resources/counter_bv_true.cfa", EXPL, NWT_IT_WP, true, 0, "Z3" },

				{ "src/test/resources/counter_bv_false.cfa", EXPL, NWT_IT_WP, false, 13, "Z3" },

				{ "src/test/resources/counter_bv_true.cfa", PRED_CART, NWT_IT_WP, true, 0, "Z3" },

				{ "src/test/resources/counter_bv_false.cfa", PRED_CART, UCB, false, 13, "Z3" },

				{ "src/test/resources/counter_bv_true.cfa", EXPL, SEQ_ITP, true, 0, "mathsat:latest" },

				{ "src/test/resources/counter_bv_false.cfa", EXPL, SEQ_ITP, false, 13, "mathsat:latest" },

				{ "src/test/resources/fp1.cfa", PRED_CART, NWT_IT_WP, true, 0, "Z3" },

				{ "src/test/resources/fp2.cfa", PRED_CART, NWT_IT_WP, false, 5, "Z3" },

				{ "src/test/resources/counter_fp_true.cfa", EXPL, NWT_IT_WP, true, 0, "Z3" },

				{ "src/test/resources/ifelse.cfa", PRED_CART, SEQ_ITP, false, 3, "Z3" },

				{ "src/test/resources/ifelse.cfa", PRED_BOOL, BW_BIN_ITP, false, 3, "Z3" },

				{ "src/test/resources/ifelse.cfa", EXPL, SEQ_ITP, false, 3, "Z3" },

				{ "src/test/resources/locking.cfa", PRED_CART, SEQ_ITP, true, 0, "Z3" },

		});
	}

	@Test
	public void test() throws Exception {
		SolverManager.registerSolverManager(Z3SolverManager.create());
		if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
			SolverManager.registerSolverManager(SmtLibSolverManager.create(SmtLibSolverManager.HOME, NullLogger.getInstance()));
		}

		final SolverFactory solverFactory;
		try {
			solverFactory = SolverManager.resolveSolverFactory(solver);
		}
		catch (Exception e) {
			Assume.assumeNoException(e);
			return;
		}

		try {
			CFA cfa = CfaDslManager.createCfa(new FileInputStream(filePath));
			CfaConfig<? extends State, ? extends Action, ? extends Prec> config
				= new CfaConfigBuilder(domain, refinement, solverFactory).build(cfa, cfa.getErrorLoc().get());
			SafetyResult<? extends State, ? extends Action> result = config.check();
			Assert.assertEquals(isSafe, result.isSafe());
			if (result.isUnsafe()) {
				Trace<CfaState<ExplState>, CfaAction> trace = CfaTraceConcretizer.concretize(
					(Trace<CfaState<?>, CfaAction>) result.asUnsafe().getTrace(),
					solverFactory);
				Assert.assertEquals(cexLength, trace.length());
			}
		}
		finally {
			SolverManager.closeAll();
		}
	}


}
