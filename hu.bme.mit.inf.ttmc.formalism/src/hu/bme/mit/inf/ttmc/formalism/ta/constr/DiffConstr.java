package hu.bme.mit.inf.ttmc.formalism.ta.constr;

public interface DiffConstr extends AtomicConstr {

	public Clock getLeftClock();

	public Clock getRightClock();

}
