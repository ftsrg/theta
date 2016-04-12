package hu.bme.mit.inf.ttmc.core;

import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.core.factory.impl.DeclFactoryImpl;
import hu.bme.mit.inf.ttmc.core.factory.impl.ExprFactoryImpl;
import hu.bme.mit.inf.ttmc.core.factory.impl.TypeFactoryImpl;

public class ConstraintManagerImpl implements ConstraintManager {

	private final DeclFactory declFactory;
	private final TypeFactory typeFactory;
	private final ExprFactory exprFactory;

	public ConstraintManagerImpl() {
		declFactory = new DeclFactoryImpl();
		typeFactory = new TypeFactoryImpl();
		exprFactory = new ExprFactoryImpl();
	}

	@Override
	public DeclFactory getDeclFactory() {
		return declFactory;
	}

	@Override
	public TypeFactory getTypeFactory() {
		return typeFactory;
	}

	@Override
	public ExprFactory getExprFactory() {
		return exprFactory;
	}

	@Override
	public SolverFactory getSolverFactory() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
