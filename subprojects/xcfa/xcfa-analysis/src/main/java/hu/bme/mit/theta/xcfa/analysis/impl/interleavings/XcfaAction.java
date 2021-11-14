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
package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaAction extends hu.bme.mit.theta.xcfa.analysis.common.XcfaAction {
	private final Integer process;
	private final List<XcfaLabel> labels;
	private final XcfaLocation source;
	private final XcfaLocation target;

	protected XcfaAction(final Integer process, final XcfaLocation source, final XcfaLocation target, final List<XcfaLabel> labels) {
		this.process = checkNotNull(process);
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.labels = checkNotNull(labels);
	}

	public static XcfaAction create(final Integer process, final XcfaEdge edge) {
		return new XcfaAction(process, edge.getSource(), edge.getTarget(), edge.getLabels());
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

	public boolean touchesGlobal() {
		return labels.stream().anyMatch(label -> LabelUtils.isGlobal(label, source.getParent().getParent().getParent()));
	}

	public Integer getProcess() {
		return process;
	}

	public XcfaAction withLabels(final List<XcfaLabel> stmts) {
		return new XcfaAction(process, source, target, stmts);
	}
}
