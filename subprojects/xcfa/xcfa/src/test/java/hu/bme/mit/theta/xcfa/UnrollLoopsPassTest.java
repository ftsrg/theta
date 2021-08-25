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

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnrollLoopsPass;
import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class UnrollLoopsPassTest {


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
		XcfaEdge e2 = new XcfaEdge(L0, L2, List.of());
		XcfaEdge e3 = new XcfaEdge(L1, L0, List.of());
		XcfaEdge e4 = new XcfaEdge(L2, L3, List.of());
		XcfaEdge e5 = new XcfaEdge(L3, L4, List.of());
		XcfaEdge e6 = new XcfaEdge(L3, L0, List.of());
		XcfaEdge e7 = new XcfaEdge(L4, L5, List.of());
		XcfaEdge e8 = new XcfaEdge(L4, Lf, List.of());
		XcfaEdge e9 = new XcfaEdge(L5, L2, List.of());
		builder.addEdge(e1);
		builder.addEdge(e2);
		builder.addEdge(e3);
		builder.addEdge(e4);
		builder.addEdge(e5);
		builder.addEdge(e6);
		builder.addEdge(e7);
		builder.addEdge(e8);
		builder.addEdge(e9);

		XcfaPassManager.clearProcedurePasses();
		String original = copyBuilder(builder).build().toDot(List.of(), List.of());

		XcfaPassManager.clearProcedurePasses();
		XcfaPassManager.addProcedurePass(new UnrollLoopsPass());
		String unrolled1 = copyBuilder(builder).build().toDot(List.of(), List.of());

		XcfaPassManager.clearProcedurePasses();
		XcfaPassManager.addProcedurePass(new UnrollLoopsPass());
		XcfaPassManager.addProcedurePass(new UnrollLoopsPass());
		String unrolled2 = copyBuilder(builder).build().toDot(List.of(), List.of());

		System.out.println("digraph G{");
		System.out.println("subgraph cluster_0 {");
		System.out.println(original);
		System.out.println("}");
		System.out.println("subgraph cluster_1 {");
		System.out.println(unrolled1);
		System.out.println("}");
		System.out.println("subgraph cluster_2 {");
		System.out.println(unrolled2);
		System.out.println("}");
		System.out.println("}");
	}

	private XcfaProcedure.Builder copyBuilder(XcfaProcedure.Builder builder) {
		XcfaProcedure.Builder ret = XcfaProcedure.builder();
		Map<XcfaLocation, XcfaLocation> locationLut = new LinkedHashMap<>();
		builder.getLocs().forEach(location -> {
			XcfaLocation copy = XcfaLocation.copyOf(location);
			ret.addLoc(copy);
			locationLut.put(location, copy);
		});
		ret.setFinalLoc(locationLut.get(builder.getFinalLoc()));
		ret.setInitLoc(locationLut.get(builder.getInitLoc()));
		if(builder.getErrorLoc() != null) ret.setErrorLoc(locationLut.get(builder.getErrorLoc()));
		for (XcfaEdge edge : builder.getEdges()) {
			ret.addEdge(new XcfaEdge(locationLut.get(edge.getSource()), locationLut.get(edge.getTarget()), edge.getStmts()));
		}
		return ret;
	}

}
