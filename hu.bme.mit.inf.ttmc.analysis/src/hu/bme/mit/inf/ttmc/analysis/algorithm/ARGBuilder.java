package hu.bme.mit.inf.ttmc.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.common.Product2;

class ARGBuilder<S extends State, NodeLabel, EdgeLabel, Init, Trans, Target> {

	private final AnalysisContext<? super S, Init, Trans, Target> context;
	private final ARGLabeling<? super S, NodeLabel, EdgeLabel, ? super Init, ? super Trans, ? super Target> labeling;

	private final Domain<S> domain;
	private final TargetPredicate<? super S, Target> targetPredicate;

	ARGBuilder(final AnalysisContext<? super S, Init, Trans, Target> context,
			final ARGLabeling<? super S, NodeLabel, EdgeLabel, ? super Init, ? super Trans, ? super Target> labeling,
			final Domain<S> domain, final TargetPredicate<? super S, Target> targetPredicate) {
		this.context = checkNotNull(context);
		this.labeling = checkNotNull(labeling);
		this.domain = checkNotNull(domain);
		this.targetPredicate = checkNotNull(targetPredicate);
	}

	public <P extends Precision> ARG<S, NodeLabel, EdgeLabel> create(final InitFunction<S, P, Init> initFunction,
			final P precision) {
		checkNotNull(initFunction);
		checkNotNull(precision);

		final Init init = context.getInitialization();
		final Target target = context.getTarget();
		final Collection<? extends S> initStates = initFunction.getInitStates(precision, init);

		final ARG<S, NodeLabel, EdgeLabel> arg = new ARG<>(domain);

		for (final S initState : initStates) {
			final boolean isTarget = targetPredicate.isTargetState(initState, target);
			final ARGNode<S, NodeLabel, EdgeLabel> initNode = arg.createInitNode(initState, isTarget);
			initNode.label = labeling.getLabelForInitNode(initNode, init, target);
		}

		return arg;
	}

	public <P extends Precision> void expand(final ARG<S, NodeLabel, EdgeLabel> arg,
			final ARGNode<S, NodeLabel, EdgeLabel> node, final TransferFunction<S, P, Trans> transferFunction,
			final P precision) {
		checkNotNull(arg);
		checkNotNull(node);
		checkNotNull(transferFunction);
		checkNotNull(precision);

		if (node.isExpanded()) {
			return;
		}

		final Target target = context.getTarget();

		final Collection<? extends Trans> transitions = context.getTransitions(node.getState());
		for (final Trans trans : transitions) {
			final Collection<S> succStates = transferFunction.getSuccStates(node.getState(), precision, trans);
			for (final S succState : succStates) {
				final boolean isTarget = targetPredicate.isTargetState(succState, target);
				final ARGNode<S, NodeLabel, EdgeLabel> succNode = arg.createSuccNode(node, succState, isTarget);
				final Product2<EdgeLabel, NodeLabel> labels = labeling.getLabelForSuccNode(succNode, trans, target);
				if (labels != null) {
					succNode.inEdge.get().label = labels._1();
					succNode.label = labels._2();
				}
			}
		}

		node.expanded = true;
	}

}
