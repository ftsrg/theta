package hu.bme.mit.inf.ttmc.analysis.zone;

enum DBMRelation {
	LESS(true, false), GREATER(false, true), EQUAL(true, true), DISJOINT(false, false);

	private final boolean leq;
	private final boolean geq;

	private DBMRelation(final boolean leq, final boolean geq) {
		this.leq = leq;
		this.geq = geq;
	}

	public static DBMRelation create(final boolean leq, final boolean geq) {
		if (leq) {
			if (geq) {
				return DBMRelation.EQUAL;
			} else {
				return DBMRelation.LESS;
			}
		} else {
			if (geq) {
				return DBMRelation.GREATER;
			} else {
				return DBMRelation.DISJOINT;
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
