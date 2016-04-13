package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.impl.STSExprFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.impl.VarDeclFactoryImpl;
import hu.bme.mit.inf.ttmc.solver.SolverFactory;
import hu.bme.mit.inf.ttmc.solver.SolverManager;

public class STSManagerImpl implements STSManager {

	final TypeFactory typeFactory;
	final VarDeclFactory declFactory;
	final STSExprFactory exprFactory;
	final SolverManager solverManager;

	public STSManagerImpl(final SolverManager solverManager) {
		final ConstraintManager constraintManager = new ConstraintManagerImpl();
		typeFactory = constraintManager.getTypeFactory();
		declFactory = new VarDeclFactoryImpl(constraintManager.getDeclFactory());
		exprFactory = new STSExprFactoryImpl(constraintManager.getExprFactory());
		this.solverManager = solverManager;
	}

	public STSManagerImpl() {
		this(null);
	}

	@Override
	public VarDeclFactory getDeclFactory() {
		return declFactory;
	}

	@Override
	public TypeFactory getTypeFactory() {
		return typeFactory;
	}

	@Override
	public STSExprFactory getExprFactory() {
		return exprFactory;
	}

	@Override
	public SolverFactory getSolverFactory() {
		if (solverManager == null) {
			throw new UnsupportedOperationException();
		}
		return solverManager.getSolverFactory();
	}

}
