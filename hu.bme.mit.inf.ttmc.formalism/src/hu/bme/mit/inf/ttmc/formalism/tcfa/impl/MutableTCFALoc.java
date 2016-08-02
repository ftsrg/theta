package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class MutableTCFALoc implements TCFALoc {

	private final String name;
	private final boolean urgent;
	private final Collection<Expr<? extends BoolType>> invars;

	final Collection<MutableTCFAEdge> inEdges;
	final Collection<MutableTCFAEdge> outEdges;

	MutableTCFALoc(final String name, final boolean urgent,
			final Collection<? extends Expr<? extends BoolType>> invars) {
		this.name = name;
		this.urgent = urgent;
		this.invars = ImmutableSet.copyOf(invars);
		inEdges = new LinkedList<>();
		outEdges = new LinkedList<>();

	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public boolean isUrgent() {
		return urgent;
	}

	@Override
	public Collection<Expr<? extends BoolType>> getInvars() {
		return invars;
	}

	////

	@Override
	public Collection<? extends TCFAEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<? extends TCFAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	////

	@Override
	public String toString() {
		return "TCFALoc(" + name + ")";
	}

}
