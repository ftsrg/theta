package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Lens;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.itp.ItpState;

import java.util.Collection;
import java.util.Objects;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;

public final class BasicAlgorithmStrategy<SConcr extends State, S extends State, A extends Action> implements AlgorithmStrategy<SConcr, SConcr, S, A> {

    private final Lens<S, ? extends State> lens;
    private final PartialOrd<SConcr> partialOrd;
    private final Function<S, ?> projection;
    private final InitAbstractor<SConcr, SConcr> initAbstractor;

    public BasicAlgorithmStrategy(final Lens<S, ? extends State> lens) {
        this.lens = checkNotNull(lens);
        partialOrd = (s1, s2) -> s1.isBottom() || s1.equals(s2);
        projection = s -> lens.get(s);
        initAbstractor = s -> s;
    }

    @Override
    public final Function<S, ?> getProjection() {
        return projection;
    }

    @Override
    public InitAbstractor<SConcr, SConcr> getInitAbstractor() {
        return initAbstractor;
    }

    @Override
    public PartialOrd<SConcr> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public final boolean mightCover(ArgNode<S, A> coveree, ArgNode<S, A> coverer) {
        assert lens.get(coveree.getState()).equals(lens.get(coverer.getState()));
        return true;
    }

    @Override
    public final void cover(ArgNode<S, A> coveree, ArgNode<S, A> coverer, Collection<ArgNode<S, A>> uncoveredNodes) {
    }

    @Override
    public final void block(ArgNode<S, A> node, A action, S succState, Collection<ArgNode<S, A>> uncoveredNodes) {
        assert lens.get(succState).isBottom();
    }
}
