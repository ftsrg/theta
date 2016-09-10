package hu.bme.mit.theta.analysis.algorithm.impl;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public final class ArgEdge<S extends State, A extends Action> {

	private final ArgNode<S, A> source;
	private final ArgNode<S, A> target;
	private final A action;

	ArgEdge(final ArgNode<S, A> source, final A action, final ArgNode<S, A> target) {
		this.source = source;
		this.action = action;
		this.target = target;
	}

	public ArgNode<S, A> getSource() {
		return source;
	}

	public ArgNode<S, A> getTarget() {
		return target;
	}

	public A getAction() {
		return action;
	}

}
