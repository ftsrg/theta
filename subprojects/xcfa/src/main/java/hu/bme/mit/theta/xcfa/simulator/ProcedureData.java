package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * Stores static procedure data needed by CallState.
 * Wrapper for XCFA.Procedure.
 * TODO use this wrapper to cache data calculated every time in CallState (e.g. Transitions from StmtTransition)
 */
public class ProcedureData {
	private Procedure procedure;

	private static Map<Procedure, ProcedureData> procedureDataCache;

	public static ProcedureData getInstance(Procedure procedure) {
		if (procedureDataCache == null)
			procedureDataCache = new HashMap<>();
		ProcedureData result = new ProcedureData(procedure);
		procedureDataCache.put(procedure, result);
		return result;
	}

	private ProcedureData(Procedure procedure) {
		this.procedure = procedure;
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

	public Location getInitLoc() {
		return procedure.getInitLoc();
	}

	public Location getErrorLoc() {
		return procedure.getErrorLoc();
	}

	public int getParamSize() {
		return procedure.getParams().size();
	}

	public VarDecl<? extends Type> getParam(int i) {
		return procedure.getParams().get(i);
	}

	public Location getFinalLoc() {
		return procedure.getFinalLoc();
	}

	public Optional<VarDecl<?>> getResultVar() {
		return procedure.getResult() == null ? Optional.empty() : Optional.of(procedure.getResult());
	}
}
