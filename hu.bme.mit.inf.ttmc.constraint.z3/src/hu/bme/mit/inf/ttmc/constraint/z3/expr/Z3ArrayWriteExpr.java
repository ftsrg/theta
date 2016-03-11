package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class Z3ArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		extends AbstractArrayWriteExpr<IndexType, ElemType> implements Z3Expr<ArrayType<IndexType, ElemType>> {

	private final Context context;

	private volatile com.microsoft.z3.ArrayExpr term;

	public Z3ArrayWriteExpr(final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem, final Context context) {
		super(array, index, elem);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.ArrayExpr getTerm() {
		if (term == null) {
			final Z3Expr<?> array = (Z3Expr<?>) getArray();
			final Z3Expr<?> index = (Z3Expr<?>) getIndex();
			final Z3Expr<?> elem = (Z3Expr<?>) getElem();

			final com.microsoft.z3.ArrayExpr arrayTerm = (com.microsoft.z3.ArrayExpr) array.getTerm();
			final com.microsoft.z3.Expr indexTerm = index.getTerm();
			final com.microsoft.z3.Expr elemExpr = elem.getTerm();

			term = context.mkStore(arrayTerm, indexTerm, elemExpr);
		}
		return term;
	}

}
