package hu.bme.mit.theta.formalism.xta.analysis.lazy;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;

public interface AlgorithmStrategy<S extends State> {

	public Analysis<XtaState<S>, XtaAction, UnitPrec> getAnalysis();

	public Partition<ArgNode<XtaState<S>, XtaAction>, ?> createReachedSet();

	public boolean mightCover(ArgNode<XtaState<S>, XtaAction> coveree, ArgNode<XtaState<S>, XtaAction> coverer);

	public boolean shouldExclude(final XtaState<S> state);

	public Collection<ArgNode<XtaState<S>, XtaAction>> forceCover(final ArgNode<XtaState<S>, XtaAction> coveree,
			ArgNode<XtaState<S>, XtaAction> coverer, final LazyXtaStatistics.Builder stats);

	public Collection<ArgNode<XtaState<S>, XtaAction>> block(final ArgNode<XtaState<S>, XtaAction> node,
			final XtaAction action, final XtaState<S> succState, final LazyXtaStatistics.Builder stats);

}
