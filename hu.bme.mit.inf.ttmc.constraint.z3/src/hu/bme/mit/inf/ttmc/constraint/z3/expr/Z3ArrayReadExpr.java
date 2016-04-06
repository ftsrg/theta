package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class Z3ArrayReadExpr<IndexType extends Type, ElemType extends Type>
		extends AbstractArrayReadExpr<IndexType, ElemType> implements Z3Expr<ElemType> {

	private final Context context;

	private volatile com.microsoft.z3.Expr term;

	public Z3ArrayReadExpr(final ConstraintManager manager,
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Context context) {
		super(manager, array, index);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.Expr getTerm() {
		if (term == null) {
			final Z3Expr<?> array = (Z3Expr<?>) getArray();
			final Z3Expr<?> index = (Z3Expr<?>) getIndex();

			final com.microsoft.z3.ArrayExpr arrayTerm = (com.microsoft.z3.ArrayExpr) array.getTerm();
			final com.microsoft.z3.Expr indexTerm = index.getTerm();

			term = context.mkSelect(arrayTerm, indexTerm);
		}
		return term;
	}

}
