package hu.bme.mit.theta.solver.z3;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;

final class Z3ItpMarker implements ItpMarker {

	private final Stack<com.microsoft.z3.BoolExpr> terms;

	public Z3ItpMarker() {
		terms = new StackImpl<>();
	}

	public void add(final com.microsoft.z3.BoolExpr term) {
		terms.add(checkNotNull(term));
	}

	public void push() {
		terms.push();
	}

	public void pop(final int n) {
		terms.pop(n);
	}

	public Collection<com.microsoft.z3.BoolExpr> getTerms() {
		return terms.toCollection();
	}

}