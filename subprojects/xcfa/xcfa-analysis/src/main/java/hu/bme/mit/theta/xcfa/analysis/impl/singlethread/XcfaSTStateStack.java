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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Map;
import java.util.Objects;
import java.util.Stack;
import java.util.stream.Collectors;

public class XcfaSTStateStack<S extends ExprState> extends XcfaSTState<S> {

    public static class ProcedureLocation {
        private final XcfaLocation location;
        private final Map<VarDecl<?>, VarDecl<?>> varLut;

        ProcedureLocation(XcfaLocation location) {
            this(location, location.getParent().getInstantiatedVars(new Stack<>()));
        }

        ProcedureLocation(XcfaLocation location, Map<VarDecl<?>, VarDecl<?>> varLut) {
            this.location = location;
            this.varLut = varLut;
        }

        Map<VarDecl<?>, VarDecl<?>> getUsedVars() {
            return varLut;
        }

        XcfaSTStateStack.ProcedureLocation withLocation(XcfaLocation location) {
            return new XcfaSTStateStack.ProcedureLocation(location, varLut);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            XcfaSTStateStack.ProcedureLocation that = (XcfaSTStateStack.ProcedureLocation) o;
            return location == that.location && varLut.entrySet().stream().noneMatch(entry -> that.varLut.get(entry.getKey()) != entry.getValue());
        }

        @Override
        public int hashCode() {
            return Objects.hash(location, varLut);
        }
    }

    private final Stack<XcfaSTStateStack.ProcedureLocation> locationStack;

    protected XcfaSTStateStack(final XcfaLocation currentLoc, final S globalState) {
        super(globalState);
        this.locationStack = new Stack<>();
        this.locationStack.push(new XcfaSTStateStack.ProcedureLocation(currentLoc));
    }

    private XcfaSTStateStack(final Stack<XcfaSTStateStack.ProcedureLocation> locationStack, final S globalState) {
        super(globalState);
        this.locationStack = new Stack<>();
        this.locationStack.addAll(locationStack);
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
        return locationStack.peek().location;
    }

    public Stack<XcfaSTStateStack.ProcedureLocation> getCurrentStack() {
        return locationStack;
    }

    public Map<VarDecl<?>, VarDecl<?>> getCurrentVars() {
        return locationStack.peek().varLut;
    }

    public Map<VarDecl<?>, VarDecl<?>> getReverseVars() {
        return this.getCurrentVars().entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
    }

    XcfaLocation pop() {
        return locationStack.pop().location;
    }

    void push(XcfaLocation location) {
        Stack<XcfaLocation> stack = new Stack<>();
        locationStack.forEach(procLoc -> stack.push(procLoc.location));
        Map<VarDecl<?>, VarDecl<?>> varLut = location.getParent().getInstantiatedVars(stack);
        locationStack.push(new XcfaSTStateStack.ProcedureLocation(location, varLut));
        updateParams();
    }

    private void updateParams() {
        Map<VarDecl<?>, VarDecl<?>> callingProcedureAltVars = locationStack.get(locationStack.size() - 2).location.getParent().getAltVars();
        Map<VarDecl<?>, VarDecl<?>> callingProcedureVars = locationStack.get(locationStack.size() - 2).varLut;
        callingProcedureAltVars.forEach((var, altVar) -> {
            if (callingProcedureVars.get(var) != null) // calling proc has the same var instantiated
                locationStack.peek().varLut.put(altVar, callingProcedureVars.get(var));
        });
    }

    @Override
    public boolean equalLocations(XcfaSTState<?> o) {
        XcfaSTStateStack<?> that = (XcfaSTStateStack<?>) o;
        if (locationStack.size() != that.locationStack.size()) return false;
        for (int i = 0; i < locationStack.size(); ++i)
            if (!Objects.equals(locationStack.get(i), that.locationStack.get(i))) return false;
        return true;
    }

    @Override
    public int hashCode() {
        return Objects.hash(locationStack, globalState);
    }

    public XcfaSTStateStack<S> withState(final S succState) {
        return new XcfaSTStateStack<>(this.locationStack, succState);
    }

    public XcfaSTStateStack<S> withLocation(final XcfaLocation location) {
        XcfaSTStateStack<S> state = new XcfaSTStateStack<>(this.locationStack, this.globalState);
        XcfaSTStateStack.ProcedureLocation top = state.locationStack.pop();
        state.locationStack.push(top.withLocation(location));
        return state;
    }
}
