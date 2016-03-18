package hu.bme.mit.inf.ttmc.cegar.common.data;

import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

import java.util.Iterator;
import java.util.List;

/**
 * Class representing a concrete trace.
 * @author Akos
 */
public class ConcreteTrace implements Iterable<AndExpr>{
	private List<AndExpr> trace;
	private boolean isCounterexample;

	/**
	 * Initialize trace
	 * @param trace Trace
	 * @param isCounterexample Is the trace a counterexample
	 */
	public ConcreteTrace(List<AndExpr> trace, boolean isCounterexample) {
		this.trace = trace;
		this.isCounterexample = isCounterexample;
	}

	/**
	 * Get the trace
	 * @return Trace
	 */
	public List<AndExpr> getTrace() {
		return trace;
	}

	/**
	 * Get the a specific state
	 * @param i Index of the state
	 * @return State specified by the index
	 */
	public Expr<? extends Type> getState(int i) {
		return trace.get(i);
	}

	/**
	 * Get the length of the trace
	 * @return Length of the trace
	 */
	public int size() {
		return trace.size();
	}

	/**
	 * Get whether the trace is a counterexample
	 * @return True if the trace is a counterexample, false otherwise
	 */
	public boolean isCounterexample() {
		return isCounterexample;
	}

	@Override
	public Iterator<AndExpr> iterator() {
		return trace.iterator();
	}
}
