package hu.bme.mit.inf.ttmc.constraint;

import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;

/**
 *
 * @author Tamás Tóth
 *
 */
public interface ConstraintManager {

	public DeclFactory getDeclFactory();

	public TypeFactory getTypeFactory();

	public ExprFactory getExprFactory();

	public SolverFactory getSolverFactory();

}
