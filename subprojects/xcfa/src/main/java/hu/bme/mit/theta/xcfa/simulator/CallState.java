package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

/**
 * Call state stores data (and is responsible) of one call (not a procedure, rather an instance of it being called)
 * For example, a recursion might have more callstate of the same procedure at a given moment.
 *
 * Naming:
 * procedure Caller() {
 *     L1 -> L2 {
 *         callerResultVar := call Callee(callerParamVar1, callerParamVar2)
 *     }
 * }
 *
 * procedure Callee(calleeParam1 : int, calleeParamVar2 : int) {
 * 	   var result : int // calleeResultVar
 *     L1 -> L2 {
 *         result := 123
 *     }
 * }
 *
 * TODO remove implicit type checks
 */
public final class CallState implements StmtExecutorInterface {

	/**
	 * Stores which procedure is called
	 */
	private ProcedureData procData;

	/**
	 * Stores the current location of the procedure, or the location to return to, when there is a method call inside.
	 */
	private Location currentLocation;

	/**
	 * The ProcessState the call belongs to
	 *
	 * The whole state is wrapped up in RuntimeState which consists of multiple ProcessStates,
	 * which consists of multiple CallStates in a tree-like structure.
	 */
	private ProcessState parent;

	/**
	 * The variable to be filled with the result when the procedure ends
	 * null means result is not expected by the caller (e.g. call foo() instead of bar := call foo())
	 */
	private VarDecl<? extends Type> callerResultVar;

	/**
	 * Constructor
	 *
	 * The result is not expected, when call foo() is used instead of bar := foo() (callerResultVar is null)
	 *
	 * @param parent The ProcessState it belongs to
	 * @param procData The procedure (independent of state) which is called
	 * @param callerParameters the parameter variables passed (the caller side, not the function)
	 * @param callerResultVar the variable to be filled when the procedure ends. If null, a result is not expected
	 */
	public CallState(ProcessState parent, ProcedureData procData, List<VarDecl<?>> callerParameters, VarDecl<?> callerResultVar) {
		this.parent = parent;
		this.procData = procData;
		this.callerResultVar = callerResultVar;
		currentLocation = procData.getInitLoc();
		begin(callerParameters);
	}

	/**
	 * Shorthand for constructor without expected return value
	 *
	 * The result is not expected, when call foo() is used instead of bar := foo() (callerResultVar is null).
	 * @param parent The ProcessState it belongs to
	 * @param procData The procedure (independent of state) which is called
	 * @param callerParameters the parameter variables passed (the caller side, not the function)
	 */
	public CallState(ProcessState parent, ProcedureData procData, List<VarDecl<?>> callerParameters) {
		this(parent, procData, callerParameters, null);
	}

	/**
	 * CPP-style copy constructor. Used by DFS to be able to "revert" a transition
	 *
	 * Used by ProcessState (and indirectly, by RuntimeState) when copying the whole explicit state of a program
	 * @param stepParent The already copied parent ProcessState
	 * @param toCopy The CallState to copy
	 */
	public CallState(ProcessState stepParent, CallState toCopy) {
		parent = stepParent;
		procData = toCopy.procData;
		currentLocation = toCopy.currentLocation;
		callerResultVar = toCopy.callerResultVar;
	}

	private RuntimeState getRuntimeState() {
		return parent.getRuntimeState();
	}

	/** Evaluates the variable given the stack state and variable valuation */
	private <DeclType extends Type> Optional<LitExpr<DeclType>> evalVariable(VarDecl<DeclType> variable) {
		return getRuntimeState().evalVariable(variable);
	}

	/**
	 * Called when the procedure gets called.
	 * Pushes local variable instances.
	 */
	public void begin(List<VarDecl<?>> callerParameters) {

		/* The order is important:
		 * 1. Evaluate caller parameter values (it should be enough to remember the indexing at this point)
		 * 2. "Push" parameters & locals "to stack"
		 * 3. Copy caller parameter values to callees'
		 *
		 * gcd(big,little) call to gcd(little,big%little) must not change little's value
		 */
		// TODO this could be checked statically...
		Preconditions.checkArgument(callerParameters.size() == procData.getParamSize(), "Procedure has wrong number of parameters passed.");

		// so it's basically the same as gcd(a',b') { gcd(a':=b,b':=a%b) }

		// evaluate the parameters
		List<Optional<? extends LitExpr<?>>> callerParamValues = new ArrayList<>();
		for (VarDecl<?> param: callerParameters) {
			callerParamValues.add(evalVariable(param));
		}

		procData.pushProcedure(getRuntimeState());

		// go through all parameters and initialize them
		for (int i = 0; i < callerParameters.size(); i++) {
			VarDecl calleeParam = procData.getParam(i);
			// Uninitialized parameter value means that the callee parameter will be uninitialized too
			callerParamValues.get(i).ifPresent(litExpr -> getRuntimeState().updateVariable(calleeParam, litExpr));
		}
	}

	/**
	 * Called when the function gets returned.
	 * Deletes values associated with the current values.
	 */
	public void end() {

		/* The order is important:
		 * 1. Calculate return value from the current context
		 * 2. Pop parameters & locals "from stack" (also remove now unused values from the valuation)
		 * 3. Write result to caller's variable
		 */
		Optional<? extends LitExpr> resultValue = Optional.empty();
		if (procData.getResultVar().isPresent()) {
			resultValue = evalVariable(procData.getResultVar().get());
		}

		procData.popProcedure(getRuntimeState());

		if (resultValue.isPresent()) {
			Preconditions.checkState(callerResultVar != null, "Procedure has variable called return, but caller expects none.");

			getRuntimeState().updateVariable(callerResultVar, (LitExpr)resultValue.get());
		} else {
			Preconditions.checkState(callerResultVar == null, "Procedure has no variable named return, but caller expects one.");
		}

		// tell parent we are finished
		parent.pop();
	}

	public void collectEnabledTransitions(RuntimeState x, Collection<Transition> transitions) {
		if (currentLocation == procData.getFinalLoc()) {
			transitions.add(new LeaveTransition(parent.getProcess()));
			return;
		}
		boolean alreadyAddedOne = false;
		for (XCFA.Process.Procedure.Edge edge : currentLocation.getOutgoingEdges()) {
			// TODO multiple stmts on an edge is not fully supported
			Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
			for (Stmt stmt : edge.getStmts()) {
				StmtTransition tr = new StmtTransition(parent.getProcess(), edge);
				if (tr.enabled(getRuntimeState())) {
					Preconditions.checkState(!alreadyAddedOne, "Only 1 edge should be active in a given process.");
					alreadyAddedOne = true;
					transitions.add(tr);
				}
			}
		}
	}

	private boolean isErrorLocation() {
		return currentLocation == procData.getErrorLoc();
	}

	public void updateLocation(Location target) throws ErrorReachedException {
		currentLocation = target;
		if (isErrorLocation()) {
			// TODO Rework: now as the Simulator is not part of the test suite, getting to the error location is not an error
			throw new ErrorReachedException("Error location reached!");
		}
	}

	public void call(CallStmt stmt) {
		ProcessState process = parent;
		if (stmt.isVoid()) {
			process.push(stmt.getProcedure(), stmt.getParams());
		} else {
			process.push(stmt.getProcedure(), stmt.getParams(), stmt.getVar());
		}
	}

	public void assign(AssignStmt<?> stmt) {
		getRuntimeState().assign(stmt);
	}

	private void havocVariable(VarDecl<?> var) {
		getRuntimeState().havocVariable(var);
	}

	public void havoc(HavocStmt<?> stmt) {
		havocVariable(stmt.getVarDecl());
	}
}
