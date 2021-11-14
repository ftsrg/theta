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
package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class XcfaSTAction extends hu.bme.mit.theta.xcfa.analysis.common.XcfaAction {
	private final List<XcfaLabel> labels;
	private final XcfaLocation source;
	private final XcfaLocation target;

	protected XcfaSTAction(final XcfaLocation source, final XcfaLocation target, final List<XcfaLabel> labels) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.labels = checkNotNull(labels);
		checkState(labels.stream().noneMatch(label -> label instanceof XcfaLabel.StartThreadXcfaLabel), "Cannot use single-threaded analysis for multi-threaded programs!");
	}

	public static XcfaSTAction create(final XcfaEdge edge) {
		return new XcfaSTAction(edge.getSource(), edge.getTarget(), edge.getLabels());
	}

	public XcfaLocation getSource() {
		return source;
	}

	public XcfaLocation getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return labels.stream().map(XcfaLabel::getStmt).collect(Collectors.toList());
	}

	public List<XcfaLabel> getLabels() {
		return labels;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(labels).toString();
	}

	public XcfaSTAction withLabels(final List<XcfaLabel> stmts) {
		return new XcfaSTAction(source, target, stmts);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaSTAction that = (XcfaSTAction) o;
		return labels.equals(that.labels) && source.equals(that.source) && target.equals(that.target);
	}

	@Override
	public int hashCode() {
		return Objects.hash(labels, source, target);
	}
}
