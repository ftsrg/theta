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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

public final class CfaAction extends StmtAction {

	private final List<Edge> edges;
	private final List<Stmt> stmts;
	private final Loc source;
	private final Loc target;

	private CfaAction(final Loc source, final Loc target, final List<Edge> edges) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.edges = Collections.unmodifiableList(checkNotNull(edges));
		this.stmts = Collections.unmodifiableList(edges.stream().map(Edge::getStmt).collect(Collectors.toList()));
	}

	public static CfaAction create(final Edge edge) {
		return new CfaAction(edge.getSource(), edge.getTarget(), Collections.singletonList(edge));
	}

	public static CfaAction create(final List<Edge> edges) {
		checkArgument(!edges.isEmpty(), "Empty list of edges");
		for (int i = 0; i < edges.size() - 1; ++i) {
			checkArgument(edges.get(i).getTarget().equals(edges.get(i + 1).getSource()));
		}
		final Loc source = edges.get(0).getSource();
		final Loc target = edges.get(edges.size() - 1).getTarget();
		return new CfaAction(source, target, edges);
	}

	public Loc getSource() {
		return source;
	}

	public Loc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	public List<Edge> getEdges() {
		return edges;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(stmts).toString();
	}
}
