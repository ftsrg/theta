package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

public class CallState implements StmtExecutorInterface {
	/**
	 * current location, or where-to-return (after returning from current call)
	 */
	private ProcedureData procData;
	private Location currentLocation;
	private ProcessState parent;
	/**
	 * Where to return the result
	 */
	private Optional<VarDecl<?>> callerResultVar;

	public CallState(ProcessState parent, ProcedureData procData, List<VarDecl<?>> parameters, VarDecl<?> callerResultVar) {
		this.parent = parent;
		this.procData = procData;
		this.callerResultVar = (callerResultVar == null ? Optional.empty() : Optional.of(callerResultVar));
		currentLocation = procData.getInitLoc();
		begin(parameters);
	}

	public CallState(ProcessState parent, ProcedureData procData, List<VarDecl<?>> parameters) {
		this(parent, procData, parameters, null);
	}

	public CallState(ProcessState stepParent, CallState toCopy) {
		parent = stepParent;
		procData = toCopy.procData;
		currentLocation = toCopy.currentLocation;
		callerResultVar = toCopy.callerResultVar;
	}

	private RuntimeState getRuntimeState() {
		return parent.parent;
	}

	private void updateCurrentValue(VarDecl<?> variable, LitExpr<?> newValue) {
		getRuntimeState().valuation.put(getCurrentVar(variable), newValue);
	}

	private <DeclType extends Type> Optional<LitExpr<DeclType>> evaluateVariable(VarDecl<DeclType> variable) {
		return getRuntimeState().valuation.eval(getCurrentVar(variable));
	}
	/**
	 * Called when the procedure gets called.
	 * Pushes local variable instances.
	 */
	public void begin(List<VarDecl<?>> parameters) {

		// TODO this could be checked statically...
		Preconditions.checkArgument(parameters.size() == procData.getParamSize(), "Procedure has wrong number of parameters passed.");

		//  map everything *first* to the indexed version, because modifying the numbering can have effect to the variables
		// for example: gcd(a,b) call to gcd(b,a%b) would change `a`'s meaning first
		// so it's basically the same as gcd(a',b') { gcd(a':=b,b':=a%b) }

		// evaluate the parameters
		List<Optional<? extends LitExpr<?>>> callerParamValues = new ArrayList<>();
		for (VarDecl<?> param: parameters) {
			Decl<? extends Type> callerIndexedParam = getCurrentVar(param);
			callerParamValues.add(parent.parent.valuation.eval(callerIndexedParam));
		}

		procData.pushProcedure(parent.parent);

		// go through all parameters and initialize them
		for (int i = 0; i < parameters.size(); i++) {
			Optional<? extends LitExpr<?>> callerParameterValue = callerParamValues.get(i);

			VarDecl<?> calleeParam = procData.getParam(i);

			Decl<?> calleeParamIndexed = getCurrentVar(calleeParam);

			// Uninitialized parameter value means that the callee parameter will be uninitialized too
			callerParameterValue.ifPresent(litExpr -> parent.parent.valuation.put(calleeParamIndexed, litExpr));
		}
	}

	private<DeclType extends Type> IndexedConstDecl<DeclType> getCurrentVar(VarDecl<DeclType> var) {
		return var.getConstDecl(getRuntimeState().vars.get(var));
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
		Optional<? extends LitExpr<?>> resultValue = Optional.empty();
		Optional<Decl<? extends Type>> calleeResultVarIndexed = procData.getCurrentResultVar(getRuntimeState());
		if (calleeResultVarIndexed.isPresent()) {
			resultValue = parent.parent.valuation.eval(calleeResultVarIndexed.get());
		}

		procData.popProcedure(getRuntimeState());

		// write result
		if (calleeResultVarIndexed.isPresent()) {
			// return variable should have been written to...
			Preconditions.checkState(resultValue.isPresent(), "Procedure has return value, but return value is not used.");
			Preconditions.checkState(callerResultVar.isPresent(), "Procedure has variable called return, but return value is not used.");

			Decl<? extends Type> resultDecl = getCurrentVar(callerResultVar.get());
			parent.parent.valuation.put(resultDecl, resultValue.get());
		} else {
			Preconditions.checkState(!resultValue.isPresent(), "Procedure has no return value, but return value is used.");
			Preconditions.checkState(!callerResultVar.isPresent(), "Procedure has no variable named return, but return value is used.");
		}

		// tell parent we are finished
		parent.pop();
	}

	public void collectEnabledTransitions(RuntimeState x, Collection<Transition> transitions) {
		if (currentLocation == procData.getFinalLoc()) {
			transitions.add(new LeaveTransition(parent.process));
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
					transitions.add(new StmtTransition(parent.process, edge));
				}
			}
		}
	}

	private boolean isErrorLocation() {
		return currentLocation == procData.getErrorLoc();
	}

	public void updateLocation(Location target) {
		currentLocation = target;
		if (isErrorLocation()) {
			// TODO Rework: now as the Simulator is not part of the test suite, getting to the error location is not an error
			throw new RuntimeException("Error location reached!");
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
		RuntimeState state = getRuntimeState();
		Expr<? extends Type> unfolded = PathUtils.unfold(stmt.getExpr(), state.vars);

		FillValuation.getInstance().fill(unfolded, state.valuation);
		LitExpr x = unfolded.eval(state.valuation);
		updateCurrentValue(stmt.getVarDecl(), x);
	}

	private void removeCurrentVariable(VarDecl<?> var) {
		getRuntimeState().valuation.remove(getCurrentVar(var));
	}

	public void havoc(HavocStmt<?> stmt) {
		removeCurrentVariable(stmt.getVarDecl());
	}
}
