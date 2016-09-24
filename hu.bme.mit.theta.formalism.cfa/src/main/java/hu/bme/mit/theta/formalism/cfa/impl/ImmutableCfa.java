package hu.bme.mit.theta.formalism.cfa.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.formalism.cfa.impl.ImmutableCfaEdge.CFAEdgeBuilder;
import hu.bme.mit.theta.formalism.cfa.impl.ImmutableCfaLoc.CFALocBuilder;

public final class ImmutableCfa implements CFA {

	final ImmutableCfaLoc initLoc;
	final ImmutableCfaLoc finalLoc;
	final ImmutableCfaLoc errorLoc;
	final Collection<ImmutableCfaLoc> locs;
	final Collection<ImmutableCfaEdge> edges;

	private ImmutableCfa(final CFABuilder builder) {
		builder.cfa = this;

		initLoc = builder.initLoc.build();
		finalLoc = builder.finalLoc.build();
		errorLoc = builder.errorLoc.build();

		final ImmutableSet.Builder<ImmutableCfaLoc> locSet = ImmutableSet.builder();
		for (CFALocBuilder loc : builder.locs) {
			locSet.add(loc.build());
		}
		locs = locSet.build();

		final ImmutableSet.Builder<ImmutableCfaEdge> edgeSet = ImmutableSet.builder();
		for (CFAEdgeBuilder edge : builder.edges) {
			edgeSet.add(edge.build());
		}
		edges = edgeSet.build();
	}

	////

	public static CFA copyOf(final CFA cfa) {
		final Map<CfaLoc, CFALocBuilder> locToBuilder = new HashMap<>();
		final Collection<CFAEdgeBuilder> edgeBuilders = new HashSet<>();

		final CFABuilder cfaBuilder = new CFABuilder();

		for (CfaLoc loc : cfa.getLocs()) {
			final CFALocBuilder locBuilder = new CFALocBuilder();
			locToBuilder.put(loc, locBuilder);
		}

		for (CfaEdge edge : cfa.getEdges()) {
			final CFAEdgeBuilder edgeBuilder = new CFAEdgeBuilder(edge.getStmts());
			edgeBuilders.add(edgeBuilder);
			edgeBuilder.setSource(locToBuilder.get(edge.getSource()));
			edgeBuilder.setTarget(locToBuilder.get(edge.getTarget()));
			locToBuilder.get(edge.getSource()).addOutEdge(edgeBuilder);
			locToBuilder.get(edge.getTarget()).addInEdge(edgeBuilder);
		}

		cfaBuilder.locs.addAll(locToBuilder.values());
		cfaBuilder.edges.addAll(edgeBuilders);

		cfaBuilder.initLoc = locToBuilder.get(cfa.getInitLoc());
		cfaBuilder.finalLoc = locToBuilder.get(cfa.getFinalLoc());
		cfaBuilder.errorLoc = locToBuilder.get(cfa.getErrorLoc());

		final CFA result = cfaBuilder.build();
		return result;
	}

	////

	@Override
	public CfaLoc getInitLoc() {
		return initLoc;
	}

	@Override
	public CfaLoc getFinalLoc() {
		return finalLoc;
	}

	@Override
	public CfaLoc getErrorLoc() {
		return errorLoc;
	}

	@Override
	public Collection<? extends CfaLoc> getLocs() {
		return locs;
	}

	@Override
	public Collection<? extends CfaEdge> getEdges() {
		return edges;
	}

	////

	final static class CFABuilder {
		private ImmutableCfa cfa;

		private CFALocBuilder initLoc;
		private CFALocBuilder finalLoc;
		private CFALocBuilder errorLoc;
		private Collection<CFALocBuilder> locs;
		private Collection<CFAEdgeBuilder> edges;

		CFABuilder() {
			locs = new HashSet<>();
			edges = new HashSet<>();
		}

		public CFA build() {
			if (this.cfa == null) {
				new ImmutableCfa(this);
			}

			return cfa;
		}
	}
	
}
