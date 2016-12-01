package hu.bme.mit.theta.formalism.tcfa;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

final class SimpleTcfaLoc implements TcfaLoc {

	private final String name;
	private final boolean urgent;
	private final Collection<Expr<? extends BoolType>> invars;

	final Collection<SimpleTcfaEdge> inEdges;
	final Collection<SimpleTcfaEdge> outEdges;

	SimpleTcfaLoc(final String name, final boolean urgent,
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
	public Collection<? extends TcfaEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<? extends TcfaEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	////

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("TcfaLoc").add(name).toString();
	}

}
