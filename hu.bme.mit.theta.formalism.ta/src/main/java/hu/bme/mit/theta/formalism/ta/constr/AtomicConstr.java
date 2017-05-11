package hu.bme.mit.theta.formalism.ta.constr;

public abstract class AtomicConstr implements ClockConstr {

	private final int bound;

	public AtomicConstr(final int bound) {
		this.bound = bound;
	}

	public final int getBound() {
		return bound;
	}

}
