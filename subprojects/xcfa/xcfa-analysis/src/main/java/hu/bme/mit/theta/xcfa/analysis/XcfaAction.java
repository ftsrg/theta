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
package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Collections;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaAction extends StmtAction {

	private final XcfaEdge edge;
	private final List<Stmt> stmts;
	private final XcfaLocation source;
	private final XcfaLocation target;

	private XcfaAction(final XcfaLocation source, final XcfaLocation target, final XcfaEdge edge) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.edge = checkNotNull(edge);
		this.stmts = Collections.unmodifiableList(edge.getStmts());
	}

	public static XcfaAction create(final XcfaEdge edge) {
		return new XcfaAction(edge.getSource(), edge.getTarget(), edge);
	}

	public XcfaLocation getSource() {
		return source;
	}

	public XcfaLocation getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	public XcfaEdge getEdge() {
		return edge;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(stmts).toString();
	}
}
