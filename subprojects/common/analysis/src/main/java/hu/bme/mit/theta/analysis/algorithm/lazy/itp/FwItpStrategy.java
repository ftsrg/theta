package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.utils.Lens;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public final class FwItpStrategy<SConcr extends State, SAbstr extends ExprState, SItp extends State, S extends State, A extends Action, P extends Prec, PAbstr extends Prec>
    extends BinItpStrategy<SConcr, SAbstr, SItp, S, A, P> {

    private final TransFunc<SAbstr, A, PAbstr> transFunc;
    private final PAbstr abstrPrec;

    public FwItpStrategy(final Lens<S, LazyState<SConcr, SAbstr>> lens,
                         final Lattice<SAbstr> abstrLattice,
                         final Interpolator<SAbstr, SItp> interpolator,
                         final Concretizer<SConcr, SAbstr> concretizer,
                         final InvTransFunc<SItp, A, P> invTransFunc,
                         final P prec,
                         final TransFunc<SAbstr, A, PAbstr> transFunc,
                         final PAbstr abstrPrec){
        super(lens, abstrLattice, concretizer, interpolator, invTransFunc, prec);
        this.transFunc = checkNotNull(transFunc);
        this.abstrPrec = checkNotNull(abstrPrec);
    }

    @Override
    public final SAbstr block(final ArgNode<S, A> node, final SItp B, final Collection<ArgNode<S, A>> uncoveredNodes){

        final SAbstr abstrState = lens.get(node.getState()).getAbstrState();
        if(interpolator.refutes(abstrState, B)){
            return abstrState;
        }

        SAbstr interpolant;

        if(node.getInEdge().isPresent()){
            final ArgEdge<S, A> inEdge = node.getInEdge().get();
            final A action = inEdge.getAction();
            final ArgNode<S, A> parent = inEdge.getSource();
            interpolant = abstrLattice.top();

            final Collection<? extends SItp> pre = invTransFunc.getPreStates(B, action, prec);
            for (final SItp B_pre : pre) {

                final SAbstr A_pre = block(parent, B_pre, uncoveredNodes);

                final Collection<? extends SAbstr> post = transFunc.getSuccStates(A_pre, action, abstrPrec);
                assert post.size() == 1;
                final SAbstr A = post.iterator().next();

                final SAbstr i = interpolator.interpolate(A, B);
                interpolant = abstrLattice.meet(i, interpolant);
            }
        } else {
            final SAbstr A = concretizer.concretize(lens.get(node.getState()).getConcrState());
            interpolant = interpolator.interpolate(A, B);
        }

        strengthen(node, interpolant);
        maintainCoverage(node, interpolant, uncoveredNodes);

        return interpolant;
    }
}
