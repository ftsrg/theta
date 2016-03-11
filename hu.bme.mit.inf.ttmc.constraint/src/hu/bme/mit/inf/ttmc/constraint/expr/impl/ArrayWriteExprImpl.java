package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ArrayWriteExprImpl<IndexType extends Type, ElemType extends Type>
		extends AbstractArrayWriteExpr<IndexType, ElemType> {

	public ArrayWriteExprImpl(Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			Expr<? extends IndexType> index, Expr<? extends ElemType> elem) {
		super(array, index, elem);
	}

}
