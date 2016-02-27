package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class TypeInferrer {

	@SuppressWarnings("unused")
	private final ConstraintManager manager;
	
	public TypeInferrer(final ConstraintManager manager) {
		this.manager = checkNotNull(manager);
	}
	
	public <T extends Type> T getType(Expr<T> expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
