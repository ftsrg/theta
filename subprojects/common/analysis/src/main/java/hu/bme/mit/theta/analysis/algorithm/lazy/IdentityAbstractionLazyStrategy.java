package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;

import java.util.Collection;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;

public final class IdentityAbstractionLazyStrategy<SConcr extends State, S extends State, A extends Action>
      implements LazyStrategy<SConcr, SConcr, S, A> {

    private final Lens<S, SConcr> lens;
    private final PartialOrd<SConcr> partialOrd;
    private final Function<S, SConcr> projection;
    private final Concretizer<SConcr, SConcr> concretizer;
    private final InitAbstractor<SConcr, SConcr> initAbstractor;

    public IdentityAbstractionLazyStrategy(final Lens<S, SConcr> lens,
                                           final Concretizer<SConcr, SConcr> concretizer) {
        this.lens = checkNotNull(lens);
        this.concretizer = checkNotNull(concretizer);
        partialOrd = (s1, s2) -> s1.isBottom() || s1.equals(s2);
        projection = s -> lens.get(s);
        initAbstractor = s -> s;
    }

    @Override
    public final Function<S, SConcr> getProjection() {
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
    public boolean inconsistentState(final SConcr state) {
        return concretizer.inconsistentConcrState(state);
    }

    @Override
    public final boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer) {
        assert lens.get(coveree.getState()).equals(lens.get(coverer.getState()));
        return true;
    }

    @Override
    public final void cover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer,
                            final Collection<ArgNode<S, A>> uncoveredNodes,
                            final LazyStatistics.Builder stats) {
    }

    @Override
    public final void disable(final ArgNode<S, A> node, final A action, final S succState,
                              final Collection<ArgNode<S, A>> uncoveredNodes,
                              final LazyStatistics.Builder stats) {
        assert lens.get(succState).isBottom();
    }
}
