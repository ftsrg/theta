package hu.bme.mit.inf.theta.formalism.common.automaton;

public interface Edge<L extends Loc<L, E>, E extends Edge<L, E>> {

	public L getSource();

	public L getTarget();

}
