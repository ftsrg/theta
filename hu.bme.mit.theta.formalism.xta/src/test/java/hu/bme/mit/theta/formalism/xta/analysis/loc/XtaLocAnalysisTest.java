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
package hu.bme.mit.theta.formalism.xta.analysis.loc;

import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

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

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStmtAnalysis;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.product.Tuple;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

@RunWith(Parameterized.class)
public final class XtaLocAnalysisTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/critical-2-25-50.xta" },

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
	public void test() {
		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final LTS<XtaLocState<?>, XtaAction> lts = XtaLocLts.create(system);
		@SuppressWarnings("unchecked")
		final Analysis<ExplState, StmtAction, ExplPrec> explAnalysis = ExplStmtAnalysis.create(solver,
				And(system.getDataVars().stream().filter(v -> v.getType().equals(Int()))
						.map(v -> Eq((Expr<IntType>) v.getRef(), Int(0))).collect(toImmutableList())

				), 0);
		final ExplPrec explPrec = ExplPrec.of(system.getDataVars());
		final Analysis<XtaLocState<ExplState>, XtaAction, ExplPrec> analysis = XtaLocAnalysis.create(system,
				explAnalysis);

		final ArgBuilder<XtaLocState<ExplState>, XtaAction, ExplPrec> argBuilder = ArgBuilder.create(lts, analysis,
				s -> false);

		final Abstractor<XtaLocState<ExplState>, XtaAction, ExplPrec> abstractor = BasicAbstractor.builder(argBuilder)
				.projection(s -> Tuple.of(s.getLocs(), s.getState())).build();

		final ARG<XtaLocState<ExplState>, XtaAction> arg = abstractor.createArg();
		abstractor.check(arg, explPrec);

		System.out.println(GraphvizWriter.getInstance().writeString(ArgVisualizer.getDefault().visualize(arg)));
	}

}
