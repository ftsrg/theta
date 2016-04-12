package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.VarDeclFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.impl.STSExprFactoryImpl;

public class STSManagerImpl implements STSManager {

	final ConstraintManager manager;
	final VarDeclFactory declFactory;
	final STSExprFactory exprFactory;

	public STSManagerImpl(final ConstraintManager manager) {
		checkNotNull(manager);
		this.manager = manager;
		declFactory = new VarDeclFactoryImpl(manager.getDeclFactory());
		exprFactory = new STSExprFactoryImpl(manager.getExprFactory());
	}

	@Override
	public VarDeclFactory getDeclFactory() {
		return declFactory;
	}

	@Override
	public TypeFactory getTypeFactory() {
		return manager.getTypeFactory();
	}

	@Override
	public STSExprFactory getExprFactory() {
		return exprFactory;
	}

	@Override
	public SolverFactory getSolverFactory() {
		return manager.getSolverFactory();
	}

}
