package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

import java.util.Collection;
import java.util.Objects;
import java.util.stream.Collectors;

// TODO include not just states, but somehow edges as well (and any other things?)
public class AbstractArg<S extends State, A extends Action, P extends Prec> {
	private final Collection<State> states;
	private final P prec;

	public AbstractArg(final ARG<S,A> arg, P prec) { //, final P prec){
		states = arg.getNodes().map(ArgNode::getState).collect(Collectors.toList());
		this.prec = prec;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		AbstractArg that = (AbstractArg) o;
		return (states.equals(that.states) && prec.equals(that.prec));
	}

	@Override
	public int hashCode() {
		return Objects.hash(states, prec);
	}

}

