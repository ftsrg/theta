package hu.bme.mit.inf.ttmc.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;

public class Abstractor<S extends State, P extends Precision, NodeLabel, EdgeLabel, Init, Trans, Target> {

	private final ARGBuilder<S, NodeLabel, EdgeLabel, Init, Trans, Target> builder;

	private final InitFunction<S, P, Init> initFunction;
	private final TransferFunction<S, P, Trans> transferFunction;

	private ARG<S, NodeLabel, EdgeLabel> arg;

	public Abstractor(final AnalysisContext<? super S, Init, Trans, Target> context,
			final ARGLabeling<? super S, NodeLabel, EdgeLabel, ? super Init, ? super Trans, ? super Target> labeling,
			final Domain<S> domain, final InitFunction<S, P, Init> initFunction,
			final TransferFunction<S, P, Trans> transferFunction,
			final TargetPredicate<? super S, Target> targetPredicate) {
		checkNotNull(context);
		checkNotNull(labeling);
		checkNotNull(domain);
		checkNotNull(targetPredicate);

		this.initFunction = checkNotNull(initFunction);
		this.transferFunction = checkNotNull(transferFunction);

		builder = new ARGBuilder<>(context, labeling, domain, targetPredicate);
	}

	public ARG<S, NodeLabel, EdgeLabel> getARG() {
		return arg;
	}

	public void init(final P precision) {
		arg = builder.create(initFunction, precision);
	}

	public void check(final P precision) {
		final Collection<ARGNode<S, NodeLabel, EdgeLabel>> nodes = new ArrayList<>(arg.getNodes());
		for (final ARGNode<S, NodeLabel, EdgeLabel> node : nodes) {
			if (!node.isTarget() && !node.isExpanded() && !node.isCovered()) {
				dfs(node, precision);
			}
		}
	}

	private void dfs(final ARGNode<S, NodeLabel, EdgeLabel> node, final P precision) {
		arg.close(node);
		if (!node.isCovered()) {
			builder.expand(arg, node, transferFunction, precision);
			for (final ARGEdge<S, NodeLabel, EdgeLabel> outEdge : node.getOutEdges()) {
				final ARGNode<S, NodeLabel, EdgeLabel> succNode = outEdge.getTarget();
				if (!succNode.isTarget()) {
					dfs(succNode, precision);
				}
			}
		}
	}

}
