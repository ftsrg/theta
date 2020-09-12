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
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Domain.*;
import static hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder.Refinement.*;

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

	@Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}, {4}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "src/test/resources/arithmetic-bool00.cfa", PRED_CART, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool00.cfa", PRED_BOOL, BW_BIN_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool00.cfa", EXPL, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool01.cfa", PRED_CART, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool01.cfa", PRED_BOOL, BW_BIN_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool01.cfa", EXPL, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool10.cfa", PRED_BOOL, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool10.cfa", PRED_CART, BW_BIN_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool10.cfa", EXPL, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool11.cfa", PRED_CART, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool11.cfa", PRED_BOOL, BW_BIN_ITP, false, 15 },

				{ "src/test/resources/arithmetic-bool11.cfa",  EXPL, SEQ_ITP, false, 15 },

				{ "src/test/resources/arithmetic-int.cfa", PRED_CART, SEQ_ITP, false, 13 },

				{ "src/test/resources/arithmetic-int.cfa", PRED_BOOL, BW_BIN_ITP, false, 13 },

				{ "src/test/resources/arithmetic-int.cfa",  EXPL, SEQ_ITP, false, 13 },

				{ "src/test/resources/arrays.cfa", PRED_CART, SEQ_ITP, false, 8 },

				{ "src/test/resources/arrays.cfa", PRED_BOOL, BW_BIN_ITP, false, 8 },

				{ "src/test/resources/arrays.cfa", EXPL, SEQ_ITP, false, 8 },

				{ "src/test/resources/counter5_true.cfa", PRED_BOOL, SEQ_ITP, true, 0 },

				{ "src/test/resources/counter5_true.cfa", PRED_CART, BW_BIN_ITP, true, 0 },

				{ "src/test/resources/counter5_true.cfa", EXPL, SEQ_ITP, true, 0 },

				{ "src/test/resources/counter_bv_true.cfa", EXPL, NWT_IT_WP, true, 0 },

				{ "src/test/resources/counter_bv_false.cfa", EXPL, NWT_IT_WP, false, 13 },

				{ "src/test/resources/counter_bv_true.cfa", PRED_CART, NWT_IT_WP, true, 0 },

				{ "src/test/resources/counter_bv_false.cfa", PRED_CART, UCB, false, 13 },

				{ "src/test/resources/ifelse.cfa", PRED_CART, SEQ_ITP, false, 3 },

				{ "src/test/resources/ifelse.cfa", PRED_BOOL, BW_BIN_ITP, false, 3 },

				{ "src/test/resources/ifelse.cfa", EXPL, SEQ_ITP, false, 3 },

				{ "src/test/resources/locking.cfa", PRED_CART, SEQ_ITP, true, 0 },

		});
	}

	@Test
	public void test() throws IOException {
		CFA cfa = CfaDslManager.createCfa(new FileInputStream(filePath));
		CfaConfig<? extends State, ? extends Action, ? extends Prec> config
				= new CfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance()).build(cfa);
		SafetyResult<? extends State, ? extends Action> result = config.check();
		Assert.assertEquals(isSafe, result.isSafe());
		if (result.isUnsafe()) {
			Trace<CfaState<ExplState>, CfaAction> trace = CfaTraceConcretizer.concretize(
					(Trace<CfaState<?>, CfaAction>) result.asUnsafe().getTrace(),
					Z3SolverFactory.getInstance());
			Assert.assertEquals(cexLength, trace.length());
		}
	}


}
