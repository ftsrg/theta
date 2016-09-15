package hu.bme.mit.theta.solver.impl;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.Stack;

public class ItpMarkerImpl implements ItpMarker {

	private final Stack<Expr<? extends BoolType>> assertions;
	
	public ItpMarkerImpl() {
		assertions = new StackImpl<>();
	}
	
	public void add(Expr<? extends BoolType> assertion) {
		assertions.add(assertion);
	}
	
	public void push() {
		assertions.push();
	}
	
	public void pop(final int n) {
		assertions.pop(n);
	}
	
	@Override
	public Collection<? extends Expr<? extends BoolType>> getAssertions() {
		return assertions.toCollection();
	}

}
