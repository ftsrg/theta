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

import hu.bme.mit.theta.frontend.FrontendMetadata;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaLocation {
	private final String name;
	private final List<XcfaEdge> incomingEdges;
	private final List<XcfaEdge> outgoingEdges;
	private XcfaProcedure parent;
	private boolean isErrorLoc = false;
	private boolean isEndLoc = false;

	private XcfaLocation(final String name) {
		this.name = checkNotNull(name);
		outgoingEdges = new ArrayList<>();
		incomingEdges = new ArrayList<>();
	}

	public static XcfaLocation copyOf(final XcfaLocation from) {
		XcfaLocation xcfaLocation = create(from.getName());
		FrontendMetadata.lookupMetadata(from).forEach((s, o) -> {
			FrontendMetadata.create(xcfaLocation, s, o);
		});
		return xcfaLocation;
	}

	public static XcfaLocation create(final String name) {
		return new XcfaLocation(name);
	}

	private static int counter = 0;
	public static int uniqeCounter() {
		return counter++;
	}

	public static XcfaLocation uniqeCopyOf(final XcfaLocation from) {
		XcfaLocation xcfaLocation = create(from.getName() + uniqeCounter());
		FrontendMetadata.lookupMetadata(from).forEach((s, o) -> {
			FrontendMetadata.create(xcfaLocation, s, o);
		});
		return xcfaLocation;
	}

	public String getName() {
		return name;
	}

	public List<XcfaEdge> getIncomingEdges() {
		return Collections.unmodifiableList(incomingEdges);
	}

	public void removeIncomingEdge(XcfaEdge xcfaEdge) {
		incomingEdges.remove(xcfaEdge);
	}

	void addIncomingEdge(XcfaEdge edge) {
		incomingEdges.add(edge);
	}

	public List<XcfaEdge> getOutgoingEdges() {
		return Collections.unmodifiableList(outgoingEdges);
	}

	public void removeOutgoingEdge(XcfaEdge xcfaEdge) {
		outgoingEdges.remove(xcfaEdge);
	}

	void addOutgoingEdge(XcfaEdge edge) {
		outgoingEdges.add(edge);
	}

	@Override
	public String toString() {
		return name;
	}

	public boolean isErrorLoc() {
		return isErrorLoc;
	}

	public void setErrorLoc(boolean errorLoc) {
		isErrorLoc = errorLoc;
	}

	public boolean isEndLoc() {
		return isEndLoc;
	}

	public void setEndLoc(boolean endLoc) {
		isEndLoc = endLoc;
	}

	public XcfaProcedure getParent() {
		return parent;
	}

	void setParent(XcfaProcedure xcfaProcedure) {
		this.parent = xcfaProcedure;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaLocation location = (XcfaLocation) o;
		return name.equals(location.name);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name);
	}
}
