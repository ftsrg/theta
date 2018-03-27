package hu.bme.mit.theta.core.type.arraytype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class ArrayLitExpr<IndexType extends Type, ElemType extends Type>
		implements LitExpr<ArrayType<IndexType, ElemType>> {

	private static final int HASH_SEED = 229;
	private volatile int hashCode;

	private final ParamDecl<IndexType> index;
	private final Expr<ElemType> elem;

	private ArrayLitExpr(final ParamDecl<IndexType> index, final Expr<ElemType> elem) {
		this.index = checkNotNull(index);
		this.elem = checkNotNull(elem);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayLitExpr<IndexType, ElemType> of(
			final ParamDecl<IndexType> index, final Expr<ElemType> elem) {
		return new ArrayLitExpr<>(index, elem);
	}

	public ParamDecl<IndexType> getIndex() {
		return index;
	}

	public Expr<ElemType> getElem() {
		return elem;
	}

	@Override
	public int getArity() {
		return 1;
	}

	@Override
	public ArrayType<IndexType, ElemType> getType() {
		return Array(index.getType(), elem.getType());
	}

	@Override
	public LitExpr<ArrayType<IndexType, ElemType>> eval(final Valuation val) {
		return this;
	}

	@Override
	public List<Expr<ElemType>> getOps() {
		return ImmutableList.of(elem);
	}

	@Override
	public ArrayLitExpr<IndexType, ElemType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 1);
		final Expr<ElemType> newElem = TypeUtils.cast(ops.get(0), elem.getType());
		return with(newElem);
	}

	public ArrayLitExpr<IndexType, ElemType> with(final Expr<ElemType> elem) {
		if (this.elem == elem) {
			return this;
		} else {
			return ArrayLitExpr.of(index, elem);
		}
	}

	@Override
	public int hashCode() {
		int tmp = hashCode;
		if (tmp == 0) {
			tmp = HASH_SEED;
			tmp = 31 * tmp + index.hashCode();
			tmp = 31 * tmp + elem.hashCode();
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
			return this.index.equals(that.index) && this.elem.equals(that.elem);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final String indexString = String.format("(%s %s)", index.getName(), index.getType());
		return Utils.lispStringBuilder("array").add(indexString).add(elem).toString();
	}

}
