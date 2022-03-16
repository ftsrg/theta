/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Objects;
import java.util.Stack;

public class XcfaSTState<S extends ExprState> extends XcfaState<S> {
	private final Stack<XcfaLocation> locationStack;
	private final S globalState;

	private XcfaSTState(final XcfaLocation currentLoc, final S globalState) {
		this.locationStack = new Stack<>();
		this.locationStack.push(currentLoc);
		this.globalState = globalState;
	}

	private XcfaSTState(final Stack<XcfaLocation> locationStack, final S globalState) {
		this.locationStack = new Stack<>();
		this.locationStack.addAll(locationStack);
		this.globalState = globalState;
	}

	public static <S extends ExprState> XcfaSTState<S> create(final XcfaLocation currentLoc, final S globalState) {
		return new XcfaSTState<>(currentLoc, globalState);
	}

	@Override
	public boolean isBottom() {
		return globalState.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return globalState.toExpr();
	}

	@Override
	public S getGlobalState() {
		return globalState;
	}

	@Override
	public XcfaLocation getCurrentLoc() {
		return locationStack.peek();
	}

	XcfaLocation pop() {
		return locationStack.pop();
	}

	void push(XcfaLocation location) {
		locationStack.push(location);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaSTState<?> that = (XcfaSTState<?>) o;
		if (!(globalState.equals(that.globalState) && locationStack.size() == that.locationStack.size())) return false;
		for (int i = 0; i < locationStack.size(); ++i)
			if (!Objects.equals(locationStack.get(i), that.locationStack.get(i))) return false;
		return true;
	}

	@Override
	public int hashCode() {
		return Objects.hash(locationStack, globalState);
	}

	public XcfaSTState<S> withState(final S succState) {
		return new XcfaSTState<>(this.locationStack, succState);
	}

	public XcfaSTState<S> withLocation(final XcfaLocation location) {
		return create(location, globalState);
	}
}
