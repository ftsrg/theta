package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

class CallState {
	/**
	 * current location, or where-to-return (after returning from current call)
	 */
	XCFA.Process.Procedure procedure;
	XCFA.Process.Procedure.Location currentLocation;
	ProcessState parent;
	/**
	 * Where to return the result
	 */
	Optional<VarDecl<?>> resultVar;

	public CallState(ProcessState parent, XCFA.Process.Procedure procedure, List<VarDecl<?>> parameters, VarDecl<?> resultVar) {
		this.parent = parent;
		this.procedure = procedure;
		this.resultVar = (resultVar == null ? Optional.empty() : Optional.of(resultVar));
		currentLocation = procedure.getInitLoc();
		begin(parameters);
	}

	public CallState(ProcessState parent, XCFA.Process.Procedure procedure, List<VarDecl<?>> parameters) {
		this(parent, procedure, parameters, null);
	}

	/**
	 * Called when the procedure gets called.
	 * Pushes local variable instances.
	 */
	public void begin(List<VarDecl<?>> parameters) {
		//  map everything *first* to the indexed version, because modifying the numbering can have effect to the variables
		// for example: gcd(a,b) call to gcd(b,a%b) would change `a`'s meaning first
		// so it's basically the same as gcd(a',b') { gcd(a':=b,b':=a%b) }
		List<Decl<?>> callerParamsIndexed = new ArrayList<>(parameters);
		callerParamsIndexed.replaceAll((a) -> ((VarDecl<?>) a).getConstDecl(parent.parent.vars.get((VarDecl<?>) a)));

		// TODO this could be checked statically...
		Preconditions.checkState(callerParamsIndexed.size() == procedure.getParams().size(), "Procedure has wrong number of parameters passed.");

		// TODO there is an error here in the simulator: evaluating parameters and pushing must be done in two stages
		// TODO write a test case catching the error (GCD?)

		// go through all parameters, "push stack" with VarIndexing
		for (int i = 0; i < parameters.size(); i++) {
			Decl<?> callerParamIndexed = callerParamsIndexed.get(i);
			Optional<? extends LitExpr<?>> callerParameterValue = parent.parent.valuation.eval(callerParamIndexed);

			VarDecl<?> calleeParam = procedure.getParams().get(i);

			parent.parent.vars = parent.parent.vars.inc(calleeParam);

			int calleeParamIndex = parent.parent.vars.get(calleeParam);
			Decl<?> calleeParamIndexed = calleeParam.getConstDecl(calleeParamIndex);

			// Uninitialized parameter value means that the callee parameter will be uninitialized too
			if (callerParameterValue.isPresent())
				parent.parent.valuation.put(calleeParamIndexed, callerParameterValue.get());
		}

		// "push" local variables with VarIndexing
		// result is a variable too, it is pushed here
		for (VarDecl var : procedure.getVars()) {
			parent.parent.vars = parent.parent.vars.inc(var);
		}
	}

	/**
	 * Called when the function gets returned.
	 * Deletes values associated with the current values.
	 */
	public void end() {
		// All values that must be calculated (result) must be calculated at the start of the function
		// After, all variables and parameters can be popped and removed from the valuation
		// Values are removed so a bug does not cause us to use a previous call's return value
		//  (and for memory efficiency)
		// AFTER popping the variables, we are in the caller's state, which means we can WRITE the result of the variables
		// So: calculate with callee's state, pop stack, and write result only then

		// evaluate result
		Optional<? extends LitExpr<?>> result = Optional.empty();
		if (procedure.getResult() != null) {
			int index0 = parent.parent.vars.get(procedure.getResult());
			result = parent.parent.valuation.eval(procedure.getResult().getConstDecl(index0));
		}

		// pop call-stack parameters and local variables
		for (VarDecl var : procedure.getParams()) {
			int index = parent.parent.vars.get(var);
			parent.parent.valuation.remove(var.getConstDecl(index));
			parent.parent.vars = parent.parent.vars.inc(var, -1);
		}

		// "pop" variables
		for (VarDecl var : procedure.getVars()) {
			int index = parent.parent.vars.get(var);
			parent.parent.valuation.remove(var.getConstDecl(index));
			parent.parent.vars = parent.parent.vars.inc(var, -1);
		}

		// write result
		if (procedure.getResult() != null) {
			// return variable should have been written to...
			Preconditions.checkState(result.isPresent(), "Procedure has return value, but nothing is returned.");
			Preconditions.checkState(resultVar.isPresent(), "Procedure has return value, but nothing is returned.");
			Decl<? extends Type> resultDecl = resultVar.get().getConstDecl(parent.parent.vars.get(resultVar.get()));
			parent.parent.valuation.put(resultDecl, result.get());
		} else {
			Preconditions.checkState(!result.isPresent(), "Procedure has no return value, but something is returned.");
		}

		// tell parent we are finished
		parent.pop();
	}

	// returning from a function counts as a step
	public boolean step() {
		if (currentLocation == procedure.getFinalLoc()) {
			end();
			return true;
		}
		for (XCFA.Process.Procedure.Edge edge : currentLocation.getOutgoingEdges()) {
			// TODO multiple stmts on an edge is not fully supported
			// some special stmt could mess up everything with multiple statements:
			// L0 -> L1 {
			//   call proc()
			//   a = a + 2
			// }
			// this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.

			// Because of this, currently only one stmt/edge is enforced:
			Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
			for (Stmt stmt : edge.getStmts()) {
				if (!stmt.accept(EnabledTransitionVisitor.getInstance(), parent.parent))
					continue;
				stmt.accept(StateUpdateVisitor.getInstance(), this);
				currentLocation = edge.getTarget();

				// TODO Rework: now as the Simulator is not part of the test suite, getting to the error location is not an error
				// test that the procedure did not get to the error location
				Preconditions.checkState(currentLocation != procedure.getErrorLoc(), "Test failed: Reached error location.");
				// step succeeded
				return true;
			}
		}
		return false;
	}

	public void collectEnabledTransitions(RuntimeState x, Collection<Transition> transitions) {
		// TODO create an end call statement
		if (currentLocation == procedure.getFinalLoc()) {
			transitions.add(new LeaveTransition(parent));
			return;
		}
		boolean alreadyAddedOne = false;
		for (XCFA.Process.Procedure.Edge edge : currentLocation.getOutgoingEdges()) {
			// TODO multiple stmts on an edge is not fully supported
			Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
			for (Stmt stmt : edge.getStmts()) {
				if (stmt.accept(EnabledTransitionVisitor.getInstance(), x)) {
					Preconditions.checkState(!alreadyAddedOne, "Probably only 1 edge should be active in a given process.");
					alreadyAddedOne = true;
					transitions.add(new StmtTransition(parent, edge));
				}
			}
		}
	}
}
