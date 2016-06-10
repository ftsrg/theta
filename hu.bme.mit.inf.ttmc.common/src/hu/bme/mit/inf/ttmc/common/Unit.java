package hu.bme.mit.inf.ttmc.common;

public final class Unit {

	private static final int HASH_CODE = 1261289;
	private static final String TO_STRING = "()";

	private static final Unit unit = new Unit();

	private Unit() {
	}

	public static Unit unit() {
		return unit;
	}

	@Override
	public int hashCode() {
		return HASH_CODE;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof Unit;
	}

	@Override
	public String toString() {
		return TO_STRING;
	}

}
