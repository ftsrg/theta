package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.utils.Lens;

import java.util.Collection;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Unit.unit;
import static java.util.stream.Collectors.toList;

public abstract class ItpStrategy<SConcr extends State, SAbstr extends ExprState, SItp extends State, S extends State, A extends Action, P extends Prec>
        implements LazyStrategy<SConcr, SAbstr, S, A> {

    protected final Lens<S, LazyState<SConcr, SAbstr>> lens;
    protected final Lattice<SAbstr> abstrLattice;
    protected final Interpolator<SAbstr, SItp> interpolator;
    protected final Concretizer<SConcr, SAbstr> concretizer;
    protected final InvTransFunc<SItp, A, P> invTransFunc;
    protected final P prec;
    private final Function<S, ?> projection;
    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    protected ItpStrategy(final Lens<S, LazyState<SConcr, SAbstr>> lens,
                          final Lattice<SAbstr> abstrLattice,
                          final Interpolator<SAbstr, SItp> interpolator,
                          final Concretizer<SConcr, SAbstr> concretizer,
                          final InvTransFunc<SItp, A, P> invTransFunc,
                          final P prec){
        this.lens = checkNotNull(lens);
        this.abstrLattice = checkNotNull(abstrLattice);
        this.interpolator = checkNotNull(interpolator);
        this.concretizer = checkNotNull(concretizer);
        this.invTransFunc = checkNotNull(invTransFunc);
        this.prec = checkNotNull(prec);
        projection = s -> unit();
        initAbstractor = s -> abstrLattice.top();
    }

    @Override
    public final Function<S, ?> getProjection(){
        return projection;
    }

    @Override
    public final InitAbstractor<SConcr, SAbstr> getInitAbstractor(){
        return initAbstractor;
    }

    @Override
    public final PartialOrd<SAbstr> getPartialOrd() {
        return abstrLattice;
    }

    @Override
    public final boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer){
        final SConcr covereeState = lens.get(coveree.getState()).getConcrState();
        final SAbstr covererState = lens.get(coverer.getState()).getAbstrState();
        return concretizer.proves(covereeState, covererState);
    }

    @Override
    public final void cover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer, final Collection<ArgNode<S, A>> uncoveredNodes){
        final SItp covererState = interpolator.toItpDom(lens.get(coverer.getState()).getAbstrState());
        final Collection<SItp> complementState = interpolator.complement(covererState);
        complementState.forEach(B -> block(coveree, B, uncoveredNodes));
    }

    @Override
    public final void disable(final ArgNode<S, A> node, final A action, final S succState, final Collection<ArgNode<S, A>> uncoveredNodes){
        assert succState.isBottom();
        final SItp top = interpolator.toItpDom(abstrLattice.top());
        final Collection<? extends SItp> badStates = invTransFunc.getPreStates(top, action, prec);
        badStates.forEach(B -> block(node, B, uncoveredNodes));
    }

    protected abstract SAbstr block(final ArgNode<S, A> node, final SItp B, final Collection<ArgNode<S, A>> uncoveredNodes);

    protected final void strengthen(final ArgNode<S, A> node, final SAbstr interpolant){
        final S state = node.getState();
        final LazyState<SConcr, SAbstr> lazyState = lens.get(state);
        final SAbstr abstrState = lazyState.getAbstrState();
        final SAbstr newAbstrState = abstrLattice.meet(abstrState, interpolant);
        final LazyState<SConcr, SAbstr> newLazyState = lazyState.withAbstrState(newAbstrState);
        final S newState = lens.set(state, newLazyState);
        node.setState(newState);
    }

    protected final void maintainCoverage(final ArgNode<S, A> node, final SAbstr interpolant, final Collection<ArgNode<S, A>> uncoveredNodes){
        final Collection<ArgNode<S, A>> uncovered =
                node.getCoveredNodes().filter(covered -> shouldUncover(covered, interpolant)).collect(toList());
        uncoveredNodes.addAll(uncovered);
        uncovered.forEach(ArgNode::unsetCoveringNode);
    }

    private boolean shouldUncover(final ArgNode<S, A> coveredNode, final SAbstr interpolant){
        final SAbstr coveredState = lens.get(coveredNode.getState()).getAbstrState();
        return !abstrLattice.isLeq(coveredState, interpolant);
    }
}
