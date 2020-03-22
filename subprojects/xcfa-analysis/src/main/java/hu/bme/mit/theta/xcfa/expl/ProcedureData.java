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
package hu.bme.mit.theta.xcfa.expl;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.XCFA.Process;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;

/**
 * Stores static procedure data needed by CallState.
 * Wrapper for XCFA.Procedure.
 *
 * Caches list of transitions from a given location.
 * This is especially useful if an XCFA is iterated more than once (e.g. in ExplChecker).
 *
 * Hides Location and Edge, uses ProcedureData.LocationWrapper and Transition instead. (Thus caching is enforced)
 *
 */
public class ProcedureData {
	private final Procedure procedure;
	private final Process parent;

	private final Map<Procedure.Location, LocationWrapper> map = new HashMap<>();
	private static Map<Procedure, ProcedureData> procedureDataCache;

	private LeaveTransition leaveTransition;

	/** Maps a location (described by an XCFA edge) to a ProcedureData.LocationWrapper */
	public LocationWrapper getWrappedLocation(Procedure.Location location) {
		if (!map.containsKey(location)) {
			map.put(location, new LocationWrapper(location));
		}
		return map.get(location);
	}

	public Procedure getProcedure() {
		return procedure;
	}


	/**
	 * Transition for leaving a call.
	 *
	 * A transition instance should be independent of ExplStates.
	 *
	 * Public for mocking.
	 */
	public static class LeaveTransition extends ProcessTransition {

		String procedureCanonicalName;

		public LeaveTransition(Process process, String procedureCanonicalName) {
			super(process);
			this.procedureCanonicalName = procedureCanonicalName;
		}

		@Override
		public void execute(ExplState state) {
			state.getProcessState(getProcess()).getCallStackPeek().end();
		}

		@Override
		public boolean enabled(ExplState state) {
			return true;
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder().add(procedureCanonicalName).add("leaveCall").toString();
		}
	}

	public String getCanonicalName() {
		return parent.getName() + "::" + procedure.getName();
	}

	Transition getLeaveTransition() {
		if (leaveTransition == null)
			leaveTransition = new LeaveTransition(parent, getCanonicalName());
		return leaveTransition;
	}

	public class EdgeWrapper {
		private final Stmt stmt;
		private final LocationWrapper target;
		private final LocationWrapper source;

		private EdgeWrapper(Procedure.Edge edge) {
			stmt = edge.getStmts().get(0);
			source = getWrappedLocation(edge.getSource());
			target = getWrappedLocation(edge.getTarget());
		}

		public Stmt getStmt() {
			return stmt;
		}

		public LocationWrapper getTarget() {
			return target;
		}

		public LocationWrapper getSource() {
			return source;
		}
    }

	/** Wrapper for XCFA.Procedure.Process.Location, caches list of transitions. Hides XCFA Location. */
	public class LocationWrapper {
		final Procedure.Location xcfaLocation;

		Collection<Transition> transitions = null;
		private LocationWrapper(Procedure.Location xcfaLocation) {
			this.xcfaLocation = xcfaLocation;
		}

		// aux method for collecting every location or transition
		public Collection<LocationWrapper> getEndPointLocations() {
			Collection<LocationWrapper> result = new HashSet<>();
			for (XCFA.Process.Procedure.Edge edge : xcfaLocation.getOutgoingEdges()) {
				result.add(getWrappedLocation(edge.getTarget()));
			}
			return result;
		}

		public Collection<Transition> getTransitions() {
			if (transitions != null)
				return transitions;
			transitions = new HashSet<>();
			for (XCFA.Process.Procedure.Edge edge : xcfaLocation.getOutgoingEdges()) {
				// TODO multiple stmts on an edge is not fully supported
				Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
				StmtTransition tr = new StmtTransitionImpl(parent, new EdgeWrapper(edge));
				transitions.add(tr);
			}
			return transitions;
		}
	}

	/** Assumes that tow different processes do not have common procedures */
	public static ProcedureData getInstance(Procedure procedure, Process parent) {
		if (procedureDataCache == null)
			procedureDataCache = new HashMap<>();
		if (procedureDataCache.containsKey(procedure))
			return procedureDataCache.get(procedure);
		ProcedureData result = new ProcedureData(procedure, parent);
		procedureDataCache.put(procedure, result);
		return result;
	}

	private ProcedureData(Procedure procedure, Process parent) {
		this.procedure = procedure;
		this.parent = parent;
	}

	/**
	 * VarIndexing is used for simulating the stack. This is used when this procedure is called.
	 * @param state The ExplState to be modified
	 */
	public void pushProcedure(ExplState state) {
		// result is a variable, it is already pushed here
		for (VarDecl<?> var: procedure.getLocalVars()) {
			state.pushVariable(var);
		}
		for (VarDecl<?> var: procedure.getParams()) {
			state.pushVariable(var);
		}
	}

	public void popProcedure(ExplState state) {
		for (VarDecl<?> var: procedure.getLocalVars()) {
			state.havocVariable(var);
			state.popVariable(var);
		}
		for (VarDecl<?> var: procedure.getParams()) {
			state.havocVariable(var);
			state.popVariable(var);
		}
	}

	public LocationWrapper getErrorLoc() {
		return getWrappedLocation(procedure.getErrorLoc());
	}

	public LocationWrapper getFinalLoc() {
		return getWrappedLocation(procedure.getFinalLoc());
	}

	public LocationWrapper getInitLoc() {
		return getWrappedLocation(procedure.getInitLoc());
	}

	public Collection<LocationWrapper> listAllLocations() {
		Collection<LocationWrapper> result = new HashSet<>();
		Queue<LocationWrapper> bfs = new ArrayDeque<>();
		result.add(getInitLoc());
		bfs.add(getInitLoc());
		while (!bfs.isEmpty()) {
			LocationWrapper a = bfs.remove();
			for (LocationWrapper b : a.getEndPointLocations()) {
				if (result.contains(b)) {
					continue;
				}
				bfs.add(b);
				result.add(b);
			}
		}
		return result;
	}

	public int getParamSize() {
		return procedure.getParams().size();
	}

	public VarDecl<? extends Type> getParam(int i) {
		return procedure.getParams().get(i);
	}

	public Optional<VarDecl<?>> getResultVar() {
		return procedure.getResult() == null ? Optional.empty() : Optional.of(procedure.getResult());
	}
}
