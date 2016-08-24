package hu.bme.mit.inf.theta.analysis.algorithm.impl;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.State;

public class ARGEdge<S extends State, A extends Action> {

	private final ARGNode<S, A> source;
	private final ARGNode<S, A> target;
	private final A action;

	ARGEdge(final ARGNode<S, A> source, final A action, final ARGNode<S, A> target) {
		this.source = source;
		this.action = action;
		this.target = target;
	}

	public ARGNode<S, A> getSource() {
		return source;
	}

	public ARGNode<S, A> getTarget() {
		return target;
	}

	public A getAction() {
		return action;
	}

}
