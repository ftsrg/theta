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
package hu.bme.mit.theta.cfa.cli;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

public final class CfaMetrics {
	private CfaMetrics() {}

	public static void printMetrics(Logger logger, CFA cfa){
		logger.write(Logger.Level.RESULT, "Vars: %s%n" , cfa.getVars().size());
		logger.write(Logger.Level.RESULT, "  Bool vars: %s%n" , cfa.getVars().stream().filter(v -> v.getType() instanceof BoolType).count());
		logger.write(Logger.Level.RESULT, "  Int vars: %s%n" , cfa.getVars().stream().filter(v -> v.getType() instanceof IntType).count());
		logger.write(Logger.Level.RESULT, "  Bitvector vars: %s%n" , cfa.getVars().stream().filter(v -> v.getType() instanceof BvType).count());
		logger.write(Logger.Level.RESULT, "  Array vars: %s%n" , cfa.getVars().stream().filter(v -> v.getType() instanceof ArrayType).count());
		logger.write(Logger.Level.RESULT, "Locs: %s%n" , cfa.getLocs().size());
		logger.write(Logger.Level.RESULT, "Edges: %s%n" , cfa.getEdges().size());
		logger.write(Logger.Level.RESULT, "  Assignments: %s%n" , cfa.getEdges().stream().filter(e -> e.getStmt() instanceof AssignStmt).count());
		logger.write(Logger.Level.RESULT, "  Assumptions: %s%n" , cfa.getEdges().stream().filter(e -> e.getStmt() instanceof AssumeStmt).count());
		logger.write(Logger.Level.RESULT, "  Havocs: %s%n" , cfa.getEdges().stream().filter(e -> e.getStmt() instanceof HavocStmt).count());
		logger.write(Logger.Level.RESULT, "Cyclomatic complexity: %s%n" , cfa.getEdges().size() - cfa.getLocs().size() + 2 * getCfaComponents(cfa));
	}

	public static int getCfaComponents(final CFA cfa) {
		final Set<CFA.Loc> visited = new HashSet<>();
		int components = 0;

		for (final CFA.Loc loc : cfa.getLocs()) {
			if (!visited.contains(loc)) {
				components++;
				visited.add(loc);
				final Queue<CFA.Loc> queue = new LinkedList<>();
				queue.add(loc);
				while (!queue.isEmpty()) {
					final CFA.Loc next = queue.remove();
					for (final CFA.Edge edge : next.getOutEdges()) {
						if (!visited.contains(edge.getTarget())) {
							visited.add(edge.getTarget());
							queue.add(edge.getTarget());
						}
					}
				}
			}
		}
		return components;
	}
}
