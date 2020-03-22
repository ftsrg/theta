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
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.expr.SyntheticLitExpr;
import org.antlr.v4.misc.OrderedHashMap;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Actual state of execution
 *
 * Simulates the call-stack (with where-to-return locations) for every process.
 * Stores variable values in a common Valuation.
 * Handles recursion: with VarIndexing chooses the current version of the variable is always known..
 *
 * Currently uninitialised variables only work for integers (and it assigns zero).
 *
 * Simulating multiple execution orders is possible with copy-and-execute: copy, to have the older data,
 * 	  and then execute different transitions from the 2 ExplStates.
 *
 * TODO Every global integer variable is assigned 0, because there are no sync primitives implemented yet.
 */
public final class ExplState extends AbstractExplState {
	private final Map<XCFA.Process, ProcessState> processStates;
	private final XCFA xcfa;

	/** Cached answer for getSafety(). Initialized on first call. */
	private StateSafety safety = null;

	/** Cached answer for getEnabledTransition(). Initialized on first call. */
	private Collection<Transition> enabledTransitions = null;

	/** If not null, we are in an atomic section of the given process */
	private XCFA.Process atomicLock = null;

	/**
	 * Stores all values for all versions of variables (for every depth in the stack)
	 */
	private final MutableValuation valuation;

	/**
	 * Stores the current depth of every variable.
	 * TODO use only for procedure-local vars?
	 */
	private VarIndexing vars;

	ProcessState getProcessState(XCFA.Process process) {
		return processStates.get(process);
	}

	/**
	 * Creates an initial state from the given XCFA
	 */
	public ExplState(XCFA xcfa) {
		valuation = new MutableValuation();
		vars = VarIndexing.builder(0).build();
		this.xcfa = xcfa;
		List<XCFA.Process> procs = xcfa.getProcesses();
		// init global integer vars to 0.
		for (VarDecl<? extends Type> globalVar : xcfa.getGlobalVars()) {
			if (globalVar.getType() instanceof IntType) {
				updateVariable((VarDecl<IntType>)globalVar, IntLitExpr.of(0));
			}
		}
		// The PartialOrderExplicitCheckerTest needs deterministic execution
		// independent on hash table iterating orders.
		processStates = new OrderedHashMap<>();
		for (XCFA.Process proc : procs) {
			processStates.put(proc, new ProcessState(this, proc));
		}
	}

	/**
	 * Creates an explicit state from oldState with nextTransition executed.
	 */
	private ExplState(ExplState oldState, Transition nextTransition) {
		Preconditions.checkArgument(oldState.getEnabledTransitions().contains(nextTransition));
		valuation = MutableValuation.copyOf(oldState.valuation);
		vars = oldState.vars.transform().build();
		xcfa = oldState.xcfa; // no need to copy static structure
		atomicLock = oldState.atomicLock;

		processStates = new HashMap<>();
		for (Map.Entry<XCFA.Process, ProcessState> entry : oldState.processStates.entrySet()) {
			processStates.put(entry.getKey(), new ProcessState(this, entry.getValue()));
		}

		// these will change, so we do not copy them:
		safety = null;
		enabledTransitions = null;
		nextTransition.execute(this);
	}

	/**
	 * Returns the list of enabled transitions.
	 */
	public Collection<Transition> getEnabledTransitions() {
		if (enabledTransitions != null)
			return enabledTransitions;
		// Tests require deterministic ordering of the transitions.
		Collection<Transition> result = new ArrayList<>();
		if (atomicLock == null) {
			for (Map.Entry<XCFA.Process, ProcessState> entry : processStates.entrySet()) {
				entry.getValue().collectEnabledTransitions(result);
			}
		} else {
			getProcessState(atomicLock).collectEnabledTransitions(result);
		}
		return enabledTransitions = result;
	}

	/**
	 * Enabled transitions will only be selected from this process
	 * @param process which process should start atomic execution
	 */
	void beginAtomic(XCFA.Process process) {
		Preconditions.checkState(atomicLock == null, "Atomic begin in atomic area");
		atomicLock = process;
	}

	void endAtomic() {
		Preconditions.checkState(atomicLock != null, "Atomic end without atomic begin");
		atomicLock = null;
	}

	@Override
	public Valuation getValuation() {
		return valuation;
	}

	@Override
	public ImmutableMap<XCFA.Process, ImmutableProcessState> getLocations() {
		ImmutableMap.Builder<XCFA.Process, ImmutableProcessState> builder =
				ImmutableMap.builder();
		for (ProcessState ps : processStates.values()) {
			if (ps.isFinished())
				builder.put(ps.getProcess(), new ImmutableProcessState(null));
			else
				builder.put(ps.getProcess(), new ImmutableProcessState(ps.getCallStackPeek().getLocation()));
		}
		return builder.build();
	}

	public Collection<Transition> getTransitionsOfProcess(XCFA.Process process) {
		ProcessState processState = processStates.get(process);
		if (processState.isFinished())
			return Collections.emptySet();
		CallState cs = processState.getCallStackPeek();
		ProcedureData procedureData = ProcedureData.getInstance(cs.getProcedure(), process);
		ProcedureData.LocationWrapper location = procedureData.getWrappedLocation(cs.getLocation());
		return location.getTransitions();
	}

	/** Returns the lock or an "unlocked" state. */
	public SyntheticLitExpr getLock(VarDecl<SyntheticType> syncVar) {
		return valuation.eval(syncVar).map(litExpr -> (SyntheticLitExpr)litExpr).orElse(SyntheticLitExpr.unlocked());
	}

	public boolean isLocked(VarDecl<SyntheticType> syncVar) {
		return getLock(syncVar).isLocked();
	}

	public boolean isLockedOn(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
		return isLocked(syncVar) && getLock(syncVar).getProcess() == process;
	}

	public void lock(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
		SyntheticLitExpr expr = getLock(syncVar).lock(process);
		Preconditions.checkState(!expr.isInvalid());
		valuation.put(syncVar, expr);
	}

	public void unlock(VarDecl<SyntheticType> syncVar, XCFA.Process process) {
		SyntheticLitExpr expr = getLock(syncVar).unlock(process);
		if (expr.isInvalid()) {
			safety = new StateSafety(false, false, "Bad unlocking of a mutex");
			return;
		}
		valuation.put(syncVar, expr);
	}

	public StateSafety getSafety() {
		if (safety != null)
			return safety;
		if (isFinished()) {
			return safety = new StateSafety(true, true, null);
		}
		if (!isSafe()) {
			return safety = new StateSafety(false, false, "Error location reached.");
		}
		if (getEnabledTransitions().isEmpty()) {
			return safety = new StateSafety(false, false, "Deadlock reached.");
		}
		return safety = new StateSafety(true, false, null);
	}

	/** Returns true when every thread has finished successfully,
	 * meaning that every thread has exit its main procedure. */
	private boolean isFinished() {
		for (Map.Entry<XCFA.Process, ProcessState> entry : processStates.entrySet()) {
			if (!entry.getValue().isFinished())
				return false;
		}
		return true;
	}

	private boolean isSafe() {
		for (Map.Entry<XCFA.Process, ProcessState> entry : processStates.entrySet()) {
			if (!entry.getValue().isSafe())
				return false;
		}
		return true;
	}

	/**
	 * Returns the variable to be used in the current scope.
	 *
	 * Recursive functions might have multiple versions of the same local variable.
	 * This returns the active call's version of the variable.
	 * Used by CallState and/or ProcessState.
	 * @param var Variable
	 * @param <DeclType> The type of the variable given
	 * @return Indexed variable
	 */
	private <DeclType extends Type> IndexedConstDecl<DeclType> getCurrentVar(VarDecl<DeclType> var) {
		return var.getConstDecl(vars.get(var));
	}

	/**
	 * Updates a variable with the given expression of the same type.
	 * Used by CallState and/or ProcessState.
	 */
	<DeclType extends Type> void updateVariable(VarDecl<DeclType> variable, LitExpr<DeclType> litExpr) {
		valuation.put(getCurrentVar(variable), litExpr);
	}

	/**
	 * Returns current value of the given variable.
	 * @return Returns the value or Optional.empty() when variable has no value
	 */
	<DeclType extends Type> Optional<LitExpr<DeclType>> evalVariable(VarDecl<DeclType> variable) {
		return valuation.eval(getCurrentVar(variable));
	}

	/** Interface used by CallState & ProcessState to update variable storage. */
	void havocVariable(VarDecl<? extends Type> variable) {
		valuation.remove(getCurrentVar(variable));
	}

	/** Interface used by CallState & ProcessState to update variable storage. */
	void pushVariable(VarDecl<? extends Type> variable) {
		vars = vars.inc(variable);
	}

	/** Interface used by CallState & ProcessState to update variable storage. */
	void popVariable(VarDecl<? extends Type> variable) {
		vars = vars.inc(variable, -1);
	}

	/** Interface used by CallState & ProcessState to update variable storage. */
	<DeclType extends Type> Optional<LitExpr<DeclType>> evalExpr(Expr<DeclType> expr) {
		Expr<DeclType> unfolded = PathUtils.unfold(expr, vars);
		Expr<DeclType> simplified = ExprUtils.simplify(unfolded, valuation);
		if (simplified instanceof LitExpr<?>) {
			return Optional.of((LitExpr<DeclType>) simplified);
		}
		return Optional.empty();
	}

	/** Interface used by CallState & ProcessState to update variable storage. */
	<DeclType extends Type> void assign(AssignStmt<DeclType> stmt) {
		var x = evalExpr(stmt.getExpr());
		if (x.isPresent())
			updateVariable(stmt.getVarDecl(), x.get());
		else
			havocVariable(stmt.getVarDecl());
	}

	/**
	 * Returns a new state one transition ahead, without changing `this`'s data
	 * @param transition Transition to execute in the new state
	 * @return A new state one transition ahead.
	 */
	public ExplState executeTransition(Transition transition) {
		return new ExplState(this, transition);
	}

	public ImmutableExplState toImmutableExplState() {
		return new ImmutableExplState(ImmutableValuation.copyOf(valuation), getLocations());
	}

	public static class StateSafety {
		public final boolean safe;
		public final boolean finished;
		/** Human readable message in case of unsafety. null if safe */
		public final String message;

		private StateSafety(boolean safe, boolean finished, String message) {
			this.safe = safe;
			this.finished = finished;
			this.message = message;
		}
	}
}
