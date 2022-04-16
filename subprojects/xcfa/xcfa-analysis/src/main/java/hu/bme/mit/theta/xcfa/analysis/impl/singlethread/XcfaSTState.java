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
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.*;

public class XcfaSTState<S extends ExprState> extends XcfaState<S> {

	class ProcedureLocation {
		private final XcfaLocation location;
		private final Map<VarDecl<?>, VarDecl<?>> varLut;

		ProcedureLocation(XcfaLocation location) {
			this(location, new HashMap<>());
		}

		ProcedureLocation(XcfaLocation location, Map<VarDecl<?>, VarDecl<?>> varLut) {
			this.location = location;
			this.varLut = varLut;
		}

		Collection<VarDecl<?>> getUsedVars() {
			return varLut.values();
		}

		ProcedureLocation withLocation(XcfaLocation location) {
			return new ProcedureLocation(location, varLut);
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			XcfaSTState<?>.ProcedureLocation that = (XcfaSTState<?>.ProcedureLocation) o;
			return location == that.location && varLut.entrySet().stream().noneMatch(entry -> that.varLut.get(entry.getKey()) != entry.getValue());
		}
	}

	private final Stack<ProcedureLocation> locationStack;
	private final S globalState;

	private XcfaSTState(final XcfaLocation currentLoc, final S globalState) {
		this.locationStack = new Stack<>();
		this.locationStack.push(new ProcedureLocation(currentLoc));
		this.globalState = globalState;
	}

	private XcfaSTState(final Stack<ProcedureLocation> locationStack, final S globalState) {
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
	public boolean isError() {
		return "reach_error".equals(this.getCurrentLoc().getParent().getName());
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
		return locationStack.peek().location;
	}

	public Stack<ProcedureLocation> getCurrentStack() {
		return locationStack;
	}

	public Map<VarDecl<?>, VarDecl<?>> getCurrentVars() { return locationStack.peek().varLut; }

	XcfaLocation pop() {
		return locationStack.pop().location;
	}

	void push(XcfaLocation location) {
		Map<VarDecl<?>, VarDecl<?>> varLut = new LinkedHashMap<>();
		String callCount = String.valueOf(location.getParent().getCallCount());
		for (VarDecl<?> var : location.getParent().getLocalVarMap().keySet()) {
			varLut.put(var, Decls.Var(var.getName() + callCount, var.getType()));
		}
		locationStack.push(new ProcedureLocation(location, varLut));
		updateParams();
	}

	void updateParams() {
		Map<VarDecl<?>, VarDecl<?>> calledProcedureParams = locationStack.peek().location.getParent().getParamLut();
		Map<VarDecl<?>, VarDecl<?>> procedureVars = locationStack.get(locationStack.size() - 2).varLut;
		calledProcedureParams.forEach((var, param) -> {
			if (procedureVars.get(var) != null) // calling proc has the same var
				locationStack.peek().varLut.put(param, procedureVars.get(var));
		});
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
		return new XcfaSTState<S>(this.locationStack, succState);
	}

	public XcfaSTState<S> withLocation(final XcfaLocation location) {
		XcfaSTState<S> state = new XcfaSTState<S>(this.locationStack, this.globalState);
		ProcedureLocation top = state.locationStack.pop();
		state.locationStack.push(top.withLocation(location));
		return state;
	}
}
