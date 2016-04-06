package hu.bme.mit.inf.ttmc.formalism.cfa.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.ImmutableCFAEdge.CFAEdgeBuilder;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.ImmutableCFALoc.CFALocBuilder;

public final class ImmutableCFA implements CFA {

	final ImmutableCFALoc initLoc;
	final ImmutableCFALoc finalLoc;
	final ImmutableCFALoc errorLoc;
	final Collection<ImmutableCFALoc> locs;
	final Collection<ImmutableCFAEdge> edges;

	private ImmutableCFA(final CFABuilder builder) {
		builder.cfa = this;

		initLoc = builder.initLoc.build();
		finalLoc = builder.finalLoc.build();
		errorLoc = builder.errorLoc.build();

		final ImmutableSet.Builder<ImmutableCFALoc> locSet = ImmutableSet.builder();
		for (CFALocBuilder loc : builder.locs) {
			locSet.add(loc.build());
		}
		locs = locSet.build();

		final ImmutableSet.Builder<ImmutableCFAEdge> edgeSet = ImmutableSet.builder();
		for (CFAEdgeBuilder edge : builder.edges) {
			edgeSet.add(edge.build());
		}
		edges = edgeSet.build();
	}

	////

	public static CFA copyOf(final CFA cfa) {
		final Map<CFALoc, CFALocBuilder> locToBuilder = new HashMap<>();
		final Collection<CFAEdgeBuilder> edgeBuilders = new HashSet<>();

		final CFABuilder cfaBuilder = new CFABuilder();

		for (CFALoc loc : cfa.getLocs()) {
			final CFALocBuilder locBuilder = new CFALocBuilder();
			locToBuilder.put(loc, locBuilder);
		}

		for (CFAEdge edge : cfa.getEdges()) {
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
	public CFALoc getInitLoc() {
		return initLoc;
	}

	@Override
	public CFALoc getFinalLoc() {
		return finalLoc;
	}

	@Override
	public CFALoc getErrorLoc() {
		return errorLoc;
	}

	@Override
	public Collection<? extends CFALoc> getLocs() {
		return locs;
	}

	@Override
	public Collection<? extends CFAEdge> getEdges() {
		return edges;
	}

	////

	final static class CFABuilder {
		private ImmutableCFA cfa;

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
				new ImmutableCFA(this);
			}

			return cfa;
		}
	}
	
}
