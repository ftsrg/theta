package hu.bme.mit.inf.ttmc.core;

import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;

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
