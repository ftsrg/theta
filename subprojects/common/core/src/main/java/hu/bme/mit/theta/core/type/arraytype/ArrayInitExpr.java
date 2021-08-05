package hu.bme.mit.theta.core.type.arraytype;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ArrayInitExpr<IndexType extends Type, ElemType extends Type> extends NullaryExpr<ArrayType<IndexType, ElemType>> {

	private static final int HASH_SEED = 241;
	private static final String OPERATOR_LABEL = "arrayinit";

	private final ArrayType<IndexType, ElemType> type;

	private final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems;

	private final Expr<ElemType> elseElem;

	private volatile int hashCode;

	private ArrayInitExpr(final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems,
						  final Expr<ElemType> elseElem, final ArrayType<IndexType, ElemType> type) {
		this.type = checkNotNull(type);
		this.elseElem = checkNotNull(elseElem);
		this.elems = checkNotNull(elems);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayInitExpr<IndexType, ElemType> of(
			final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems,
			final Expr<ElemType> elseElem,
			final ArrayType<IndexType, ElemType> type) {
		return new ArrayInitExpr<>(elems, elseElem, type);
	}

	public List<Tuple2<Expr<IndexType>, Expr<ElemType>>> getElements() { return ImmutableList.copyOf(elems); }

	public Expr<ElemType> getElseElem() { return elseElem; }

	@Override
	public ArrayType<IndexType, ElemType> getType() {
		return type;
	}

	@Override
	public LitExpr<ArrayType<IndexType, ElemType>> eval(final Valuation val) {
		return ArrayLitExpr.of(elems.stream().map(objects -> Tuple2.of(objects.get1().eval(val), objects.get2().eval(val))).collect(Collectors.toList()), elseElem, type);
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
		} else if (obj instanceof ArrayInitExpr) {
			final ArrayInitExpr<?, ?> that = (ArrayInitExpr<?, ?>) obj;
			return this.type.equals(that.type) && this.elems.equals(that.elems) && elseElem.equals(that.elseElem);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(OPERATOR_LABEL)
				.addAll(elems.stream().map(elem -> String.format("(%s %s)", elem.get1(), elem.get2())))
				.add((String.format("(default %s)", elseElem)))
				.toString();
	}

}
