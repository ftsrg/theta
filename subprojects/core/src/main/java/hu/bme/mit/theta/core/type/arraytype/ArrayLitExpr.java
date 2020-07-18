package hu.bme.mit.theta.core.type.arraytype;

import static com.google.common.base.Preconditions.checkNotNull;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public final class ArrayLitExpr<IndexType extends Type, ElemType extends Type> extends NullaryExpr<ArrayType<IndexType, ElemType>> 
		implements LitExpr<ArrayType<IndexType, ElemType>> {

	private static final int HASH_SEED = 229;
	private static final String OPERATOR_LABEL = "array";

	private final ArrayType<IndexType, ElemType> type;

	private final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems;

	private final Expr<ElemType> elseElem;

	private volatile int hashCode;

	private ArrayLitExpr(final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems,
						 final Expr<ElemType> elseElem, final ArrayType<IndexType, ElemType> type) {
		this.type = checkNotNull(type);
		this.elseElem = checkNotNull(elseElem);
		this.elems = checkNotNull(elems);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayLitExpr<IndexType, ElemType> of(
			final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems,
			final Expr<ElemType> elseElem,
			final ArrayType<IndexType, ElemType> type) {
		return new ArrayLitExpr<>(elems, elseElem, type);
	}

	public List<Tuple2<Expr<IndexType>, Expr<ElemType>>> getElements() { return ImmutableList.copyOf(elems); }

	public Expr<ElemType> getElseElem() { return elseElem; }

	@Override
	public ArrayType<IndexType, ElemType> getType() {
		return type;
	}

	@Override
	public LitExpr<ArrayType<IndexType, ElemType>> eval(final Valuation val) {
		return this;
	}

	@Override
	public int hashCode() {
		int tmp = hashCode;
		if (tmp == 0) {
			tmp = HASH_SEED;
			tmp = 31 * tmp + type.hashCode();
			for(Tuple2<Expr<IndexType>, Expr<ElemType>> elem : elems) {
				tmp = 31 * tmp + elem.hashCode();
			}
			hashCode = tmp;
		}
		return tmp;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ArrayLitExpr) {
			final ArrayLitExpr<?, ?> that = (ArrayLitExpr<?, ?>) obj;
			return this.type.equals(that.type) && this.elems.equals(that.elems);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final String indexString = String.format("([%s]->%s)", type.getIndexType(), type.getElemType());
		return Utils.lispStringBuilder(OPERATOR_LABEL).add(indexString).add("(")
				.addAll(elems.stream().map(elem -> String.format("([%s]->%s)", elem.get1(), elem.get2()))).add(")")
				.add((String.format("[]->%s", elseElem)))
				.toString();
	}

}
