package hu.bme.mit.theta.formalism.cfa.impl;

import java.util.Collection;
import java.util.HashSet;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.formalism.cfa.impl.ImmutableCfaEdge.CFAEdgeBuilder;

final class ImmutableCfaLoc implements CfaLoc {
	private final String name;

	final Collection<ImmutableCfaEdge> inEdges;
	final Collection<ImmutableCfaEdge> outEdges;

	ImmutableCfaLoc(final String name, final CFALocBuilder builder) {
		this.name = name;
		builder.loc = this;

		final ImmutableSet.Builder<ImmutableCfaEdge> inEdgeSet = ImmutableSet.builder();
		for (final CFAEdgeBuilder inEdge : builder.inEdges) {
			inEdgeSet.add(inEdge.build());
		}
		inEdges = inEdgeSet.build();

		final ImmutableSet.Builder<ImmutableCfaEdge> outEdgeSet = ImmutableSet.builder();
		for (final CFAEdgeBuilder outEdge : builder.outEdges) {
			outEdgeSet.add(outEdge.build());
		}
		outEdges = outEdgeSet.build();
	}

	@Override
	public Collection<? extends CfaEdge> getInEdges() {
		return inEdges;
	}

	@Override
	public Collection<? extends CfaEdge> getOutEdges() {
		return outEdges;
	}

	////

	final static class CFALocBuilder {

		private ImmutableCfaLoc loc;

		private final Collection<CFAEdgeBuilder> inEdges;
		private final Collection<CFAEdgeBuilder> outEdges;

		private final String name;

		CFALocBuilder(final String name) {
			this.name = name;
			inEdges = new HashSet<>();
			outEdges = new HashSet<>();
		}

		public ImmutableCfaLoc build() {
			if (loc == null) {
				new ImmutableCfaLoc(name, this);
			}

			return loc;
		}

		////

		public void addInEdge(final CFAEdgeBuilder inEdge) {
			inEdges.add(inEdge);
		}

		public void addOutEdge(final CFAEdgeBuilder outEdge) {
			outEdges.add(outEdge);
		}

	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(name).toString();
	}
}
