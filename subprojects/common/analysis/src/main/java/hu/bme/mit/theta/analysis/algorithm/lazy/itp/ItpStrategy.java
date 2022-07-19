package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Unit;
import hu.bme.mit.theta.core.utils.Lens;

import java.util.Collection;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Unit.unit;
import static java.util.stream.Collectors.toList;

public abstract class ItpStrategy<SConcr extends State, SAbstr extends ExprState, S extends State, A extends Action>
        implements LazyStrategy<SConcr, SAbstr, S, A> {

    protected final Lens<S, LazyState<SConcr, SAbstr>> lens;
    protected final Lattice<SAbstr> abstrLattice;
    protected final Concretizer<SConcr, SAbstr> concretizer;
    private final Function<S, Unit> projection;
    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    protected ItpStrategy(final Lens<S, LazyState<SConcr, SAbstr>> lens,
                          final Lattice<SAbstr> abstrLattice,
                          final Concretizer<SConcr, SAbstr> concretizer) {
        this.lens = checkNotNull(lens);
        this.abstrLattice = checkNotNull(abstrLattice);
        this.concretizer = checkNotNull(concretizer);
        projection = s -> unit();
        initAbstractor = s -> abstrLattice.top();

    }

    @Override
    public final Function<S, Unit> getProjection(){
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
    public boolean inconsistentState(final SConcr state) {
        return concretizer.inconsistentConcrState(state);
    }

    @Override
    public final boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer){
        final SConcr covereeState = lens.get(coveree.getState()).getConcrState();
        final SAbstr covererState = lens.get(coverer.getState()).getAbstrState();
        return concretizer.proves(covereeState, covererState);
    }

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
