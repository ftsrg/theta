package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class TypeUtils {

	private TypeUtils() {
	}

	public static boolean isLeq(final TypeFactory factory, final Type type1, final Type type2) {
		checkNotNull(factory);
		checkNotNull(type1);
		checkNotNull(type2);

		if (type1.equals(type2)) {
			return true;
		}

		if (type1 instanceof IntType && type2 instanceof RatType) {
			return true;
		}

		if (type1 instanceof FuncType<?, ?> && type2 instanceof FuncType<?, ?>) {
			final FuncType<?, ?> funcType1 = (FuncType<?, ?>) type1;
			final FuncType<?, ?> funcType2 = (FuncType<?, ?>) type2;

			return isLeq(factory, funcType2.getParamType(), funcType1.getParamType())
					&& isLeq(factory, funcType1.getResultType(), funcType2.getResultType());
		}

		if (type1 instanceof ArrayType<?, ?> && type2 instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> arrayType1 = (ArrayType<?, ?>) type1;
			final ArrayType<?, ?> arrayType2 = (ArrayType<?, ?>) type2;

			return isLeq(factory, arrayType2.getIndexType(), arrayType1.getIndexType())
					&& isLeq(factory, arrayType1.getElemType(), arrayType2.getElemType());
		}

		return false;
	}

	public static <T extends Type, T1 extends T, T2 extends T> Optional<T> join(final TypeFactory factory, final T1 type1,
			final T2 type2) {
		checkNotNull(factory);
		checkNotNull(type1);
		checkNotNull(type2);

		if (isLeq(factory, type1, type2)) {
			return Optional.of(type2);
		}

		if (isLeq(factory, type2, type1)) {
			return Optional.of(type1);
		}

		if (type1 instanceof FuncType<?, ?> && type2 instanceof FuncType<?, ?>) {
			final FuncType<?, ?> funcType1 = (FuncType<?, ?>) type1;
			final FuncType<?, ?> funcType2 = (FuncType<?, ?>) type2;
			final Optional<Type> joinResult = join(factory, funcType1.getParamType(), funcType2.getParamType());
			final Optional<Type> meetResult = meet(factory, funcType1.getResultType(), funcType2.getResultType());
			if (joinResult.isPresent() && meetResult.isPresent()) {
				final Type paramType = joinResult.get();
				final Type resultType = meetResult.get();
				final Type funcType = factory.Func(paramType, resultType);
				@SuppressWarnings("unchecked")
				final T result = (T) funcType;
				return Optional.of(result);
			}
		}

		if (type1 instanceof ArrayType<?, ?> && type2 instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> arrayType1 = (ArrayType<?, ?>) type1;
			final ArrayType<?, ?> arrayType2 = (ArrayType<?, ?>) type2;
			final Optional<Type> joinResult = join(factory, arrayType1.getIndexType(), arrayType2.getIndexType());
			final Optional<Type> meetResult = meet(factory, arrayType1.getElemType(), arrayType2.getElemType());
			if (joinResult.isPresent() && meetResult.isPresent()) {
				final Type indexType = joinResult.get();
				final Type elemType = meetResult.get();
				final Type arrayType = factory.Array(indexType, elemType);
				@SuppressWarnings("unchecked")
				final T result = (T) arrayType;
				return Optional.of(result);
			}
		}

		return Optional.empty();
	}

	public static <T extends Type, T1 extends T, T2 extends T> Optional<T> meet(final TypeFactory factory, final T1 type1,
			final T2 type2) {
		checkNotNull(factory);
		checkNotNull(type1);
		checkNotNull(type2);

		if (isLeq(factory, type1, type2)) {
			return Optional.of(type1);

		}
		if (isLeq(factory, type2, type1)) {
			return Optional.of(type2);

		}

		if (type1 instanceof FuncType<?, ?> && type2 instanceof FuncType<?, ?>) {
			final FuncType<?, ?> funcType1 = (FuncType<?, ?>) type1;
			final FuncType<?, ?> funcType2 = (FuncType<?, ?>) type2;
			final Optional<Type> meetResult = meet(factory, funcType1.getParamType(), funcType2.getParamType());
			final Optional<Type> joinResult = join(factory, funcType1.getResultType(), funcType2.getResultType());
			if (meetResult.isPresent() && joinResult.isPresent()) {
				final Type paramType = meetResult.get();
				final Type resultType = joinResult.get();
				final Type funcType = factory.Func(paramType, resultType);
				@SuppressWarnings("unchecked")
				final T result = (T) funcType;
				return Optional.of(result);
			}

		}

		if (type1 instanceof ArrayType<?, ?> && type2 instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> arrayType1 = (ArrayType<?, ?>) type1;
			final ArrayType<?, ?> arrayType2 = (ArrayType<?, ?>) type2;
			final Optional<Type> meetResult = meet(factory, arrayType1.getIndexType(), arrayType2.getIndexType());
			final Optional<Type> joinResult = join(factory, arrayType1.getElemType(), arrayType2.getElemType());
			if (meetResult.isPresent() && joinResult.isPresent()) {
				final Type indexType = meetResult.get();
				final Type elemType = joinResult.get();
				final Type arrayType = factory.Array(indexType, elemType);
				@SuppressWarnings("unchecked")
				final T result = (T) arrayType;
				return Optional.of(result);
			}
		}

		return Optional.empty();
	}

}
