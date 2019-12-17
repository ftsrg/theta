package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
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
 * The CallState implements StmtExecutorInterface to be able to update state on execution of transitions.
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
	 * Stores the current location of the procedure
	 * It stores the location to return to if there is a call active.
	 */
	private Location currentLocation;

	/**
	 * The ProcessState the call belongs to
	 *
	 * The whole state is wrapped up in ExplState which consists of multiple ProcessStates,
	 * which consists of multiple CallStates in a tree-like structure.
	 */
	private ProcessState parent;

	/**
	 * The variable to be filled with the result when the procedure ends
	 * null means result is not expected by the caller (e.g. `call foo()` instead of `bar := call foo()`)
	 * VarDecl is used to show that this is not an indexed version of the variable.
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
	CallState(ProcessState parent, ProcedureData procData, List<VarDecl<?>> callerParameters, VarDecl<?> callerResultVar) {
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
	CallState(ProcessState parent, ProcedureData procData, List<VarDecl<?>> callerParameters) {
		this(parent, procData, callerParameters, null);
	}

	/**
	 * CPP-style copy constructor.
	 *
	 * There are no need to deep copy data, but it should, if anything is needed(!)
	 *
	 * Used by ProcessState (and indirectly, by ExplState) when copying the whole explicit state of a program
	 * @param stepParent The already copied parent ProcessState
	 * @param toCopy The CallState to copy
	 */
	CallState(ProcessState stepParent, CallState toCopy) {
		parent = stepParent;
		procData = toCopy.procData;
		currentLocation = toCopy.currentLocation;
		callerResultVar = toCopy.callerResultVar;
	}

	/**
	 * Fall through
	 * @return the explicit state the CallState belongs to
	 */
	private ExplState getExplState() {
		return parent.getExplState();
	}

	/** Evaluates the variable given the stack state and variable valuation */
	private <DeclType extends Type> Optional<LitExpr<DeclType>> evalVariable(VarDecl<DeclType> variable) {
		return getExplState().evalVariable(variable);
	}

	/**
	 * Called when the procedure gets called.
	 * Pushes local variable instances.
	 */
	private void begin(List<VarDecl<?>> callerParameters) {

		/* The order is important:
		 * 1. Evaluate caller parameter values (it should be enough to remember the indexing at this point)
		 * 2. "Push" parameters & locals "to stack"
		 * 3. Copy caller parameter values to callees'
		 *
		 * gcd(big,little) call to gcd(little,big%little) must not change little's value
		 */
		// TODO this could be checked statically...
		Preconditions.checkArgument(callerParameters.size() == procData.getParamSize(), "Procedure has wrong number of parameters passed.");

		// evaluate the parameters
		List<Optional<? extends LitExpr<?>>> callerParamValues = new ArrayList<>();
		for (VarDecl<?> param: callerParameters) {
			callerParamValues.add(evalVariable(param));
		}

		procData.pushProcedure(getExplState());

		// go through all parameters and initialize them
		for (int i = 0; i < callerParameters.size(); i++) {
			VarDecl calleeParam = procData.getParam(i);
			// Uninitialized parameter value means that the callee parameter will be uninitialized too
			callerParamValues.get(i).ifPresent(litExpr -> getExplState().updateVariable(calleeParam, litExpr));
		}
	}

	/**
	 * Called when the function returns.
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

		procData.popProcedure(getExplState());

		if (resultValue.isPresent()) {
			Preconditions.checkState(callerResultVar != null, "Procedure has variable called return, but caller expects no return value.");

			getExplState().updateVariable(callerResultVar, (LitExpr)resultValue.get());
		} else {
			Preconditions.checkState(callerResultVar == null, "Procedure has no variable named return, but caller expects a return value.");
		}

		// tell parent we are finished
		parent.pop();
	}

	/**
	 * Collects transitions enabled in the given process. Called only when the call is active (at the top of the stack). Called only when the call is active (at the top of the stack).
	 * @param transitions The result will be added here
	 */
	public void collectEnabledTransitions(Collection<Transition> transitions) {
		if (currentLocation == procData.getFinalLoc()) {
			transitions.add(new LeaveTransition(parent.getProcess()));
			return;
		}
		boolean alreadyAddedOne = false;
		for (XCFA.Process.Procedure.Edge edge : currentLocation.getOutgoingEdges()) {
			// TODO multiple stmts on an edge is not fully supported
			Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
			StmtTransition tr = new StmtTransition(parent.getProcess(), edge);
			if (tr.enabled(getExplState())) {
				Preconditions.checkState(!alreadyAddedOne, "Only 1 edge should be active in a given process.");
				alreadyAddedOne = true;
				transitions.add(tr);
			}
		}
	}

	/**
	 * Updates location.
	 *
	 * Used by StmtTransition.
	 *
	 * @param target The new location
	 */
	void updateLocation(Location target) {
		currentLocation = target;
	}

	/**
	 * Called when this (active) call handles a CallStmt.
	 */
	@Override
	public void onCall(CallStmt stmt) {
		ProcessState process = parent;
		if (stmt.isVoid()) {
			process.push(stmt.getProcedure(), stmt.getParams());
		} else {
			process.push(stmt.getProcedure(), stmt.getParams(), stmt.getVar());
		}
	}

	/**
	 * Called when this active call handles an assume stmt.
	 */
	@Override
	public boolean onAssume(AssumeStmt stmt) {
		BoolLitExpr expr = (BoolLitExpr) getExplState().evalExpr(stmt.getCond());
		return expr.getValue();
	}

	/**
	 * Called when this active call handles an assignment stmt.
	 */
	@Override
	public <DeclType extends Type> void onAssign(AssignStmt<DeclType> stmt) {
		getExplState().assign(stmt);
	}

	/**
	 * Called when this active call handles havoc stmt.
	 */
	@Override
	public <DeclType extends Type> void onHavoc(HavocStmt<DeclType> stmt) {
		getExplState().havocVariable(stmt.getVarDecl());
	}

	public boolean isSafe() {
		return currentLocation != procData.getErrorLoc();
	}
}
