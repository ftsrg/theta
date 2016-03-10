package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.BoolLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public abstract class AbstractBoolLitExpr extends AbstractNullaryExpr<BoolType> implements BoolLitExpr {

	@Override
	public boolean equals(final Object obj) {
		if (obj == null) {
			return false;
		} else {
			return (this.getClass() == obj.getClass());
		}
	}

}
