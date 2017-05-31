package hu.bme.mit.theta.core.type;

public final class Types {

	private Types() {
	}

	public static IntType Int() {
		return IntType.getInstance();
	}

	public static RatType Rat() {
		return RatType.getInstance();
	}

	public static UnitType Unit() {
		return UnitType.getInstance();
	}

	public static <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		return new ArrayType<>(indexType, elemType);
	}

}
