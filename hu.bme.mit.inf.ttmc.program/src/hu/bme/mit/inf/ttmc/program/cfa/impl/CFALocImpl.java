package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.Collection;
import java.util.HashSet;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.program.cfa.impl.CFAEdgeImpl.CFAEdgeBuilder;
import hu.bme.mit.inf.ttmc.program.cfa.impl.CFAImpl.CFABuilder;

public final class CFALocImpl implements CFALoc {

	final CFA cfa;
	final Collection<CFAEdgeImpl> inEdges;
	final Collection<CFAEdgeImpl> outEdges;

	CFALocImpl(final CFALocBuilder builder) {
		builder.loc = this;

		cfa = builder.cfa.build();

		final ImmutableSet.Builder<CFAEdgeImpl> inEdgeSet = ImmutableSet.builder();
		for (CFAEdgeBuilder inEdge : builder.inEdges) {
			inEdgeSet.add(inEdge.build());
		}
		inEdges = inEdgeSet.build();

		final ImmutableSet.Builder<CFAEdgeImpl> outEdgeSet = ImmutableSet.builder();
		for (CFAEdgeBuilder outEdge : builder.inEdges) {
			outEdgeSet.add(outEdge.build());
		}
		outEdges = outEdgeSet.build();
	}

	@Override
	public CFA getCFA() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends CFAEdge> getInEdges() {
		return inEdges;
	}

	@Override
	public Collection<? extends CFAEdge> getOutEdges() {
		return outEdges;
	}

	////

	final static class CFALocBuilder {

		private CFALocImpl loc;

		private CFABuilder cfa;
		private Collection<CFAEdgeBuilder> inEdges;
		private Collection<CFAEdgeBuilder> outEdges;

		CFALocBuilder() {
			inEdges = new HashSet<>();
			outEdges = new HashSet<>();
		}

		public CFALocImpl build() {
			if (loc == null) {
				new CFALocImpl(this);
			}

			return loc;
		}

		////

		public void setCFA(final CFABuilder cfa) {
			this.cfa = cfa;
		}

		public void addInEdge(final CFAEdgeBuilder inEdge) {
			inEdges.add(inEdge);
		}

		public void addOutEdge(final CFAEdgeBuilder outEdge) {
			outEdges.add(outEdge);
		}

	}

}
