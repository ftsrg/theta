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

package hu.bme.mit.theta.xcfa.model;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.FrontendMetadata;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaEdge {
	private final XcfaLocation source;
	private final XcfaLocation target;

	private final List<XcfaLabel> labels;
	private XcfaProcedure parent;

	public XcfaEdge(final XcfaLocation source, final XcfaLocation target, final List<XcfaLabel> labels) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.labels = ImmutableList.copyOf(labels);
		source.addOutgoingEdge(this);
		target.addIncomingEdge(this);
	}

	public static XcfaEdge copyOf(XcfaEdge edge, Map<XcfaLocation, XcfaLocation> locationLut, Map<VarDecl<?>, VarDecl<?>> newVarLut) {
		List<XcfaLabel> newStmts = new ArrayList<>();
		for (XcfaLabel label : edge.getLabels()) {
			XcfaLabel label1 = label.accept(new XcfaLabelVarReplacer(), newVarLut);
			newStmts.add(label1);
		}
		XcfaEdge xcfaEdge = new XcfaEdge(locationLut.get(edge.source), locationLut.get(edge.target), newStmts);
		FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
			FrontendMetadata.create(xcfaEdge, s, o);
		});
		return xcfaEdge;
	}

	public XcfaLocation getSource() {
		return source;
	}

	public XcfaLocation getTarget() {
		return target;
	}

	public List<XcfaLabel> getLabels() {
		return labels;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("Edge").add(
				Utils.lispStringBuilder("Source").add(source)
		).add(
				Utils.lispStringBuilder("Target").add(target)
		).add(
				Utils.lispStringBuilder("Stmts").addAll(labels)
		).toString();
	}

	public XcfaProcedure getParent() {
		return parent;
	}

	void setParent(XcfaProcedure xcfaProcedure) {
		this.parent = xcfaProcedure;
	}
}
