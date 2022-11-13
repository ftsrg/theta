package hu.bme.mit.theta.core.type.arraytype;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.type.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

/**
 * ArrayInitExpr is a way to specify arbitrary array 'literals' that may contain non-literal elements as well.
 * Note that while this class is a descendant of MultiaryExpr, it is used in a non-standard way:
 *     - ops is only used as a generic Type type,
 *     - ops are solely used for inter-object interactions, intra-class the `elems` and `elseElem` are used.
 *     - `elems` and `elseElem` are mapped to `ops` by first placing the `elseElem`, then all indices, then all elements.
 */

public final class ArrayInitExpr<IndexType extends Type, ElemType extends Type> extends MultiaryExpr<Type, ArrayType<IndexType, ElemType>> {

	private static final int HASH_SEED = 241;
	private static final String OPERATOR_LABEL = "arrayinit";

	private final ArrayType<IndexType, ElemType> type;

	private final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems;

	private final Expr<ElemType> elseElem;

	private ArrayInitExpr(final List<Tuple2<Expr<IndexType>, Expr<ElemType>>> elems,
						  final Expr<ElemType> elseElem, final ArrayType<IndexType, ElemType> type) {
		//noinspection unchecked
		super(Stream.concat(List.of((Expr<Type>)elseElem).stream(), Stream.concat(elems.stream().map(objects -> (Expr<Type>)objects.get1()), elems.stream().map(objects -> (Expr<Type>)objects.get2()))).collect(Collectors.toList()));
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


	@SuppressWarnings("unchecked")
	@Override
	public MultiaryExpr<Type, ArrayType<IndexType, ElemType>> with(Iterable<? extends Expr<Type>> ops) {
		long size = StreamSupport.stream(ops.spliterator(), false).count();
		checkState(size % 2 == 1, "Ops must be odd long!");
		long counter = 0;
		Expr<ElemType> elseElem = null;
		List<Expr<IndexType>> indices = new ArrayList<>();
		List<Expr<ElemType>> elems = new ArrayList<>();
		for (Expr<Type> op : ops) {
			if(counter == 0) elseElem = (Expr<ElemType>) op;
			else if (counter <= (size-1)/2) indices.add((Expr<IndexType>) op);
			else elems.add((Expr<ElemType>) op);
			++counter;
		}
		List<Tuple2<Expr<IndexType>, Expr<ElemType>>> newOps = new ArrayList<>();
		for (int i = 0; i < indices.size(); i++) {
			newOps.add(Tuple2.of(indices.get(i), elems.get(i)));
		}
		return ArrayInitExpr.of(newOps, elseElem, type);
	}

	@Override
	public MultiaryExpr<Type, ArrayType<IndexType, ElemType>> withOps(List<? extends Expr<?>> ops) {
		return with(ops.stream().map(op -> (Expr<Type>) op).collect(Collectors.toList()));
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
