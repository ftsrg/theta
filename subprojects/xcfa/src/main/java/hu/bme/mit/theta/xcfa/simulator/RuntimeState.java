package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.*;

public class RuntimeState {
	private Map<XCFA.Process, ProcessState> processStates;
	private XCFA xcfa;
	private MutableValuation valuation;
	private VarIndexing vars;

	public ProcessState getProcessState(XCFA.Process process) {
		return processStates.get(process);
	}

	public RuntimeState(XCFA xcfa) {
		valuation = new MutableValuation();
		vars = VarIndexing.builder(0).build();
		this.xcfa = xcfa;
		List<XCFA.Process> procs = xcfa.getProcesses();
		processStates = new HashMap<>();
		for (XCFA.Process proc : procs) {
			processStates.put(proc, new ProcessState(this, proc));
		}
	}

	public RuntimeState(RuntimeState toCopy) {
		valuation = MutableValuation.copyOf(toCopy.valuation);
		vars = toCopy.vars.transform().build();
		xcfa = toCopy.xcfa; // no need to copy static structure
		processStates = new HashMap<>();
		for (Map.Entry<XCFA.Process, ProcessState> entry : toCopy.processStates.entrySet()) {
			processStates.put(entry.getKey(), new ProcessState(this, entry.getValue()));
		}
	}

	public Collection<Transition> getEnabledTransitions() {
		ArrayList<Transition> enabledTransitions = new ArrayList<>();
		for (Map.Entry<XCFA.Process, ProcessState> entry : processStates.entrySet()) {
			entry.getValue().collectEnabledTransitions(this, enabledTransitions);
		}
		return enabledTransitions;
	}

	public boolean step(Scheduler sched) throws ErrorReachedException {
		Collection<Transition> enabledTransitions = getEnabledTransitions();
		if (enabledTransitions.isEmpty()) {
			if (!isFinished()) {
				throw new ErrorReachedException("Deadlock");
			}
			return false;
		}
		sched.getNextTransition(enabledTransitions).step(this);
		return true;
	}

	/** Returns true when every thread has finished, meaning that every thread has exit its main procedure. */
	public boolean isFinished() {
		ArrayList<Transition> enabledTransitions = new ArrayList<>();
		for (Map.Entry<XCFA.Process, ProcessState> entry : processStates.entrySet()) {
			if (!entry.getValue().isFinished())
				return false;
		}
		return true;
	}

	private  <DeclType extends Type> IndexedConstDecl<DeclType> getCurrentVar(VarDecl<DeclType> var) {
		return var.getConstDecl(vars.get(var));
	}

	public <DeclType extends Type> void updateVariable(VarDecl<DeclType> variable, LitExpr<DeclType> litExpr) {
		valuation.put(getCurrentVar(variable), litExpr);
	}

	public <DeclType extends Type> Optional<LitExpr<DeclType>> evalVariable(VarDecl<DeclType> variable) {
		return valuation.eval(getCurrentVar(variable));
	}

	public void havocVariable(VarDecl<? extends Type> variable) {
		valuation.remove(getCurrentVar(variable));
	}

	public void pushVariable(VarDecl<? extends Type> variable) {
		vars = vars.inc(variable);
	}

	public void popVariable(VarDecl<? extends Type> variable) {
		vars = vars.inc(variable, -1);
	}

	public <DeclType extends Type> LitExpr<DeclType> evalExpr(Expr<DeclType> expr) {
		Expr<DeclType> unfolded = PathUtils.unfold(expr, vars);
		FillValuation.getInstance().fill(unfolded, valuation);
		return unfolded.eval(valuation);
	}
}
