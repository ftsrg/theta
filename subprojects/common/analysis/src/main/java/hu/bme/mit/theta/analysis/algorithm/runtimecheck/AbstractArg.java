package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

public class AbstractArg<S extends State, A extends Action, P extends Prec> {
	private final Collection<State> states;
	private final List<Optional<ArgEdge<S, A>>> inEdges;
	private final P prec;

	public AbstractArg(final ARG<S,A> arg, P prec) {
		inEdges = arg.getNodes().map(ArgNode::getInEdge).collect(Collectors.toList());
		states = arg.getNodes().map(ArgNode::getState).collect(Collectors.toList());
		this.prec = prec;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		AbstractArg<S,A,P> that = (AbstractArg<S,A,P>) o;
		// return (states.equals(that.states) && prec.equals(that.prec));
		return (states.equals(that.states) && prec.equals(that.prec) && inEdges.equals(that.inEdges));
	}

	@Override
	public int hashCode() {
		// return Objects.hash(states, prec);
		return Objects.hash(states, prec, inEdges);
	}

}

