package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

import java.util.Collection;
import java.util.function.Function;

public interface LazyStrategy<SConcr extends State, SAbstr extends State, S extends State, A extends Action> {

    Function<S, ?> getProjection();

    InitAbstractor<SConcr, SAbstr> getInitAbstractor();

    PartialOrd<SAbstr> getPartialOrd();

    boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer);

    void cover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer, final Collection<ArgNode<S, A>> uncoveredNodes);

    void disable(final ArgNode<S, A> node, final A action, final S succState, final Collection<ArgNode<S, A>> uncoveredNodes);
}
