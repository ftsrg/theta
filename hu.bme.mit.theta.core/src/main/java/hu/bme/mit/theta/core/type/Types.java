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

}
