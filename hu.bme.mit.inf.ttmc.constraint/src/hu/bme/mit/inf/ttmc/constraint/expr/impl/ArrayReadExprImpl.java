package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ArrayReadExprImpl<IndexType extends Type, ElemType extends Type>
		extends AbstractArrayReadExpr<IndexType, ElemType> {

	public ArrayReadExprImpl(Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			Expr<? extends IndexType> index) {
		super(array, index);
	}

}
