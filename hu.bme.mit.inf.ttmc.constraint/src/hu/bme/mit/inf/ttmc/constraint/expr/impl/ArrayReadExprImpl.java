package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ArrayReadExprImpl<IndexType extends Type, ElemType extends Type>
		extends AbstractArrayReadExpr<IndexType, ElemType> {

	public ArrayReadExprImpl(final ConstraintManager manager,
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index) {
		super(manager, array, index);
	}

}
