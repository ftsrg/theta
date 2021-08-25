/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa;

import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeRemovalPass;
import org.junit.Test;

import java.util.List;

public final class EmptyEdgeRemovalPassTest {

	@Test
	public void test(){
		XcfaProcedure.Builder builder = XcfaProcedure.builder();
		XcfaLocation L0 = new XcfaLocation("L0", null);
		XcfaLocation L1 = new XcfaLocation("L1", null);
		XcfaLocation L2 = new XcfaLocation("L2", null);
		XcfaLocation L3 = new XcfaLocation("L3", null);
		XcfaLocation L4 = new XcfaLocation("L4", null);
		XcfaLocation L5 = new XcfaLocation("L5", null);
		XcfaLocation Lf = new XcfaLocation("Lf", null);
		builder.addLoc(L0);
		builder.addLoc(L1);
		builder.addLoc(L2);
		builder.addLoc(L3);
		builder.addLoc(L4);
		builder.addLoc(L5);
		builder.addLoc(Lf);
		builder.setInitLoc(L0);
		builder.setFinalLoc(Lf);

		XcfaEdge e1 = new XcfaEdge(L0, L1, List.of());
		XcfaEdge e2 = new XcfaEdge(L1, L2, List.of());
		XcfaEdge e3 = new XcfaEdge(L2, L3, List.of(SkipStmt.getInstance()));
		XcfaEdge e4 = new XcfaEdge(L3, L4, List.of());
		XcfaEdge e5 = new XcfaEdge(L4, L5, List.of());
		XcfaEdge e6 = new XcfaEdge(L5, Lf, List.of());
		XcfaEdge e7 = new XcfaEdge(L2, L2, List.of(SkipStmt.getInstance()));
		XcfaEdge e8 = new XcfaEdge(L1, L2, List.of());
		XcfaEdge e9 = new XcfaEdge(L1, L2, List.of());
		XcfaEdge e10 = new XcfaEdge(L0, L4, List.of());

		builder.addEdge(e1);
		builder.addEdge(e2);
		builder.addEdge(e3);
		builder.addEdge(e4);
		builder.addEdge(e5);
		builder.addEdge(e6);
		builder.addEdge(e7);
		builder.addEdge(e8);
		builder.addEdge(e9);
		builder.addEdge(e10);

		XcfaPassManager.clearProcedurePasses();
		XcfaPassManager.addProcedurePass(new EmptyEdgeRemovalPass());

		String afterPass = builder.build().toDot(List.of(), List.of());

		System.out.println("digraph G{");
		System.out.println(afterPass);
		System.out.println("}");
	}

}