package hu.bme.mit.theta.analysis.zone;

enum DbmRelation {
	LESS(true, false), GREATER(false, true), EQUAL(true, true), INCOMPARABLE(false, false);

	private final boolean leq;
	private final boolean geq;

	private DbmRelation(final boolean leq, final boolean geq) {
		this.leq = leq;
		this.geq = geq;
	}

	public static DbmRelation create(final boolean leq, final boolean geq) {
		if (leq) {
			if (geq) {
				return DbmRelation.EQUAL;
			} else {
				return DbmRelation.LESS;
			}
		} else {
			if (geq) {
				return DbmRelation.GREATER;
			} else {
				return DbmRelation.INCOMPARABLE;
			}
		}
	}

	public boolean isLeq() {
		return leq;
	}

	public boolean isGeq() {
		return geq;
	}
}
