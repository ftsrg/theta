package hu.bme.mit.inf.ttmc.constraint;

import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.impl.DeclFactoryImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.impl.ExprFactoryImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.impl.TypeFactoryImpl;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeInferrer;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrerImpl;

public class ConstraintManagerImpl implements ConstraintManager {

	private final DeclFactory declFactory;
	private final TypeFactory typeFactory;
	private final ExprFactory exprFactory;
	private final TypeInferrer typeInferrer;
	
	public ConstraintManagerImpl() {
		declFactory = new DeclFactoryImpl();
		typeFactory = new TypeFactoryImpl();
		exprFactory = new ExprFactoryImpl();
		typeInferrer = new TypeInferrerImpl(typeFactory);
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

	@Override
	public TypeInferrer getTypeInferrer() {
		return typeInferrer;
	}
	
	

}
