package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public abstract class AbstractArrayType<IndexType extends Type, ElemType extends Type> extends AbstractType
		implements ArrayType<IndexType, ElemType> {

	private final static int HASH_SEED = 4919;

	private final static String TYPE_LABEL = "Array";

	private final ConstraintManager manager;

	private final IndexType indexType;
	private final ElemType elemType;

	private volatile int hashCode = 0;

	public AbstractArrayType(final ConstraintManager manager, final IndexType indexType, final ElemType elemType) {
		this.indexType = checkNotNull(indexType);
		this.elemType = checkNotNull(elemType);
		this.manager = manager;
	}

	@Override
	public final IndexType getIndexType() {
		return indexType;
	}

	@Override
	public final ElemType getElemType() {
		return elemType;
	}

	@Override
	public final Expr<ArrayType<IndexType, ElemType>> getAny() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final boolean isLeq(final Type type) {
		if (type instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) type;
			return that.getIndexType().isLeq(this.getIndexType()) && this.getElemType().isLeq(that.getElemType());
		} else {
			return false;
		}
	}

	@Override
	public final Optional<ArrayType<?, ?>> meet(final Type type) {
		if (type instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) type;
			final Optional<? extends Type> joinOfIndexTypes = this.getIndexType().join(that.getIndexType());
			final Optional<? extends Type> meetOfElemTypes = this.getElemType().meet(that.getElemType());

			if (joinOfIndexTypes.isPresent() && meetOfElemTypes.isPresent()) {
				final ArrayType<?, ?> arrayType = manager.getTypeFactory().Array(joinOfIndexTypes.get(),
						meetOfElemTypes.get());
				return Optional.of(arrayType);
			}
		}

		return Optional.empty();
	}

	@Override
	public final Optional<ArrayType<?, ?>> join(final Type type) {
		if (type instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) type;
			final Optional<? extends Type> meetOfIndexTypes = this.getIndexType().meet(that.getIndexType());
			final Optional<? extends Type> joinOfElemTypes = this.getElemType().join(that.getElemType());

			if (meetOfIndexTypes.isPresent() && joinOfElemTypes.isPresent()) {
				final ArrayType<?, ?> arrayType = manager.getTypeFactory().Array(meetOfIndexTypes.get(),
						joinOfElemTypes.get());
				return Optional.of(arrayType);
			}
		}

		return Optional.empty();
	}

	@Override
	public final <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + indexType.hashCode();
			result = 31 * result + elemType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AbstractArrayType<?, ?>) {
			final AbstractArrayType<?, ?> that = (AbstractArrayType<?, ?>) obj;
			return this.indexType.equals(that.indexType) && this.elemType.equals(that.elemType);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(TYPE_LABEL);
		sb.append("(");
		sb.append(indexType);
		sb.append(" -> ");
		sb.append(elemType);
		sb.append(")");
		return sb.toString();
	}

}
