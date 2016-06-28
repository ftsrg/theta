package hu.bme.mit.inf.ttmc.analysis.zone;

final class DiffBounds {

	private static final int INF = Integer.MAX_VALUE;

	private static final String INF_STRING = "inf";

	public static int Inf() {
		return INF;
	}

	public static int Lt(final int bound) {
		return bound << 1;
	}

	public static int Leq(final int bound) {
		return (bound << 1) | 1;
	}

	////

	public static int add(final int b1, final int b2) {
		return (b1 == INF || b2 == INF) ? INF : b1 + b2 - ((b1 & 1) | (b2 & 1));
	}

	////

	public static int getBound(final int b) {
		return b >> 1;
	}

	public static boolean isStrict(final int b) {
		return (b & 1) == 0;
	}

	public static String asString(final int b) {
		if (b == INF) {
			return INF_STRING;
		} else {
			return finiteBoundAsString(b);
		}
	}

	private static String finiteBoundAsString(final int b) {
		assert b != INF;

		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(getBound(b));
		sb.append(", ");
		if (isStrict(b)) {
			sb.append("<");
		} else {
			sb.append("<=");
		}
		sb.append(")");
		return sb.toString();
	}

}
