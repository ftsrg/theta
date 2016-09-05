package hu.bme.mit.inf.theta.solver;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.model.Model;
import hu.bme.mit.inf.theta.core.type.BoolType;

public interface Solver {
	
	public void add(Expr<? extends BoolType> assertion);
	public default void add(Collection<? extends Expr<? extends BoolType>> assertions) {
		for (Expr<? extends BoolType> assertion : assertions) {
			add(assertion);
		}
	}
	
	public void track(Expr<? extends BoolType> assertion);
	public default void track(Collection<? extends Expr<? extends BoolType>> assertions) {
		for (Expr<? extends BoolType> assertion : assertions) {
			track(assertion);
		}
	}
	
	public SolverStatus check();

	public void push();
	public void pop(final int n);
	public default void pop() {
		pop(1);
	}
	
	public void reset();
	
	public SolverStatus getStatus();
	public Model getModel();
	public Collection<Expr<? extends BoolType>> getUnsatCore();
	public Collection<Expr<? extends BoolType>> getAssertions();
}
