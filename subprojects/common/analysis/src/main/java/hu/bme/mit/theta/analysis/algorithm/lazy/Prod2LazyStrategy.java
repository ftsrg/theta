package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.prod2.Prod2Ord;
import hu.bme.mit.theta.analysis.prod2.Prod2State;

import java.util.Collection;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Prod2LazyStrategy<SConcr1 extends State, SConcr2 extends State, SAbstr1 extends State, SAbstr2 extends State, S extends State, A extends Action> implements LazyStrategy<Prod2State<SConcr1, SConcr2>, Prod2State<SAbstr1, SAbstr2>, S, A> {

    private final Lens<S, Prod2State<SConcr1, SConcr2>> lens;
    private final LazyStrategy<SConcr1, SAbstr1, S, A> strategy1;
    private final LazyStrategy<SConcr2, SAbstr2, S, A> strategy2;
    private final Function<S, ?> projection;
    private final InitAbstractor<Prod2State<SConcr1, SConcr2>, Prod2State<SAbstr1, SAbstr2>> initAbstractor;
    private final PartialOrd<Prod2State<SAbstr1, SAbstr2>> partialOrd;

    public Prod2LazyStrategy(final Lens<S, Prod2State<SConcr1, SConcr2>> lens,
                             final LazyStrategy<SConcr1, SAbstr1, S, A> strategy1,
                             final LazyStrategy<SConcr2, SAbstr2, S, A> strategy2,
                             final Function<S, ?> projection) {
        this.lens = checkNotNull(lens);
        this.strategy1 = checkNotNull(strategy1);
        this.strategy2 = checkNotNull(strategy2);
        this.projection = checkNotNull(projection);
        initAbstractor = s -> Prod2State.of(
                strategy1.getInitAbstractor().getInitAbstrState(s.getState1()),
                strategy2.getInitAbstractor().getInitAbstrState(s.getState2()));
        partialOrd = Prod2Ord.create(strategy1.getPartialOrd(), strategy2.getPartialOrd());
    }

    @Override
    public Function<S, ?> getProjection() {
        return projection;
    }

    @Override
    public InitAbstractor<Prod2State<SConcr1, SConcr2>, Prod2State<SAbstr1, SAbstr2>> getInitAbstractor() {
        return initAbstractor;
    }

    @Override
    public PartialOrd<Prod2State<SAbstr1, SAbstr2>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public boolean inconsistentState(S state) {
        return state.isBottom() ||
                strategy2.inconsistentState(state) || strategy1.inconsistentState(state);
    }

    @Override
    public boolean mightCover(ArgNode<S, A> coveree, ArgNode<S, A> coverer) {
        return strategy2.mightCover(coveree, coverer) && strategy1.mightCover(coveree, coverer);
    }

    @Override
    public void cover(ArgNode<S, A> coveree, ArgNode<S, A> coverer, Collection<ArgNode<S, A>> uncoveredNodes) {
        assert coveree.getCoveringNode().isPresent() && coveree.getCoveringNode().get().equals(coverer);
        strategy1.cover(coveree, coverer, uncoveredNodes);
        if (coveree.isCovered()){
            assert (!uncoveredNodes.contains(coveree));
            strategy2.cover(coveree, coverer, uncoveredNodes);
        }
    }

    @Override
    public void disable(ArgNode<S, A> node, A action, S succState, Collection<ArgNode<S, A>> uncoveredNodes) {
        assert inconsistentState(succState);
        Prod2State<SConcr1, SConcr2> state = lens.get(succState);
        if (state.isBottom1() || (!state.isBottom2() && strategy1.inconsistentState(succState))) {
            strategy1.disable(node, action, succState, uncoveredNodes);
        } else if (strategy2.inconsistentState(succState)) {
            strategy2.disable(node, action, succState, uncoveredNodes);
        } else {
            throw new AssertionError();
        }
    }
}
