package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.XCFA.Process;

import java.util.*;

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
	private Procedure procedure;
	private Process parent;

	private Map<Procedure.Location, LocationWrapper> map = new HashMap<>();

	/** Maps a location (described by an XCFA edge) to a ProcedureData.LocationWrapper */
	private LocationWrapper getWrappedLocation(Procedure.Location location) {
		if (!map.containsKey(location)) {
			map.put(location, new LocationWrapper(location));
		}
		return map.get(location);
	}

	private static Map<Procedure, ProcedureData> procedureDataCache;

	/**
	 * Transition for leaving a call.
	 *
	 * A transition instance should be independent of ExplStates.
	 */
	public class LeaveTransition extends ProcessTransition {

		private LeaveTransition(XCFA.Process p) {
			super(p);
		}

		@Override
		public void execute(ExplState state) {
			state.getProcessState(process).getCallStackPeek().end();
		}

		@Override
		public boolean enabled(ExplState state) {
			return true;
		}
	}

	private LeaveTransition leaveTransition;
	Transition getLeaveTransition() {
		if (leaveTransition == null)
			leaveTransition = new LeaveTransition(parent);
		return leaveTransition;
	}

	public class EdgeWrapper {
		Stmt stmt;
		LocationWrapper target;

		private EdgeWrapper(Procedure.Edge edge) {
			Preconditions.checkArgument(edge.getStmts().size() == 1,
					"ExplState supports exactly one stmt per edge");
			stmt = edge.getStmts().get(0);
			target = getWrappedLocation(edge.getTarget());
		}

		public Stmt getStmt() {
			return stmt;
		}

		public LocationWrapper getTarget() {
			return target;
		}
	}

	/** Wrapper for XCFA.Procedure.Process.Location, caches list of transitions. Hides XCFA Location. */
	public class LocationWrapper {
		Procedure.Location xcfaLocation;

		Collection<Transition> transitions = null;
		private LocationWrapper(Procedure.Location xcfaLocation) {
			this.xcfaLocation = xcfaLocation;
		}

		Collection<Transition> getTransitions() {
			if (transitions != null)
				return transitions;
			transitions = new HashSet<>();
			for (XCFA.Process.Procedure.Edge edge : xcfaLocation.getOutgoingEdges()) {
				// TODO multiple stmts on an edge is not fully supported
				Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
				StmtTransition tr = new StmtTransition(parent, new EdgeWrapper(edge));
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
		for (VarDecl<?> var: procedure.getVars()) {
			state.pushVariable(var);
		}
		for (VarDecl<?> var: procedure.getParams()) {
			state.pushVariable(var);
		}
	}

	public void popProcedure(ExplState state) {
		for (VarDecl<?> var: procedure.getVars()) {
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
