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
package hu.bme.mit.theta.xcfa.cat.solver;

import hu.bme.mit.theta.cat.solver.BoolSmtMemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.MemoryModel;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.cat.solver.programs.Program;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

@RunWith(Parameterized.class)
public class BoolSmtTest {

	@Parameterized.Parameter(value = 0)
	public MemoryModel memoryModel;

	@Parameterized.Parameter(value = 1)
	public Program program;

	@Parameterized.Parameter(value = 2)
	public boolean forbidden;

	@Parameterized.Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {
//				{new NoassertMemory(), new W2R2(), false},
//				{new CoherenceMemory(), new W2R2(), true},
//				{new NoassertMemory(), new W2R2WR(), false},
//				{new CoherenceMemory(), new W2R2WR(), true},
		});
	}

	@Test
	public void test()  {
		final MemoryModelBuilder builder = BoolSmtMemoryModelBuilder.create(memoryModel);
		final Solver solver = Z3SolverFactory.getInstance().createSolver();

		program.generateProgram(builder, solver);

		solver.check();
		if(solver.getStatus().isSat()) {
			final Valuation model = solver.getModel();
			System.err.println("po: ");
			printBinaryRelation(builder.get("po", model));
			System.err.println("===================");
			System.err.println("rf: ");
			printBinaryRelation(builder.get("rf", model));
			System.err.println("===================");
			System.err.println("co: ");
			printBinaryRelation(builder.get("co", model));
			System.err.println("===================");
			System.err.println("id: ");
			printBinaryRelation(builder.get("id", model));
			System.err.println("===================");
			System.err.println("loc: ");
			printBinaryRelation(builder.get("loc", model));
			System.err.println("===================");
			System.err.println("int: ");
			printBinaryRelation(builder.get("int", model));
			System.err.println("===================");
			System.err.println("ext: ");
			printBinaryRelation(builder.get("ext", model));
		}
		Assert.assertEquals(forbidden, solver.getStatus().isUnsat());
	}

	private void printBinaryRelation(final List<TupleN<?>> data) {
		for (TupleN<?> element : data) {
			System.err.println(element.get(0) + " -> " + element.get(1));
		}

	}

}
