package hu.bme.mit.theta.formalism.tcfa.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class NetworkTcfa implements TCFA {

	private final List<TCFA> tcfas;
	private final TcfaLoc initLoc;

	private NetworkTcfa(final List<? extends TCFA> tcfas) {
		this.tcfas = ImmutableList.copyOf(checkNotNull(tcfas));
		initLoc = new NetworkTcfaLoc(getInitLocs(tcfas));
	}

	public static NetworkTcfa of(final List<? extends TCFA> tcfas) {
		return new NetworkTcfa(tcfas);
	}

	public static NetworkTcfa of(final TCFA... tcfas) {
		return of(Arrays.asList(tcfas));
	}

	private static List<TcfaLoc> getInitLocs(final List<? extends TCFA> tcfas) {
		return tcfas.stream().map(TCFA::getInitLoc).collect(toList());
	}

	@Override
	public TcfaLoc getInitLoc() {
		return initLoc;
	}

	@Override
	public Collection<? extends TcfaLoc> getLocs() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends TcfaEdge> getEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends VarDecl<?>> getDataVars() {
		final Collection<VarDecl<?>> dataVars = new HashSet<>();
		for (final TCFA tcfa : tcfas) {
			dataVars.addAll(tcfa.getDataVars());
		}
		return Collections.unmodifiableCollection(dataVars);
	}

	@Override
	public Collection<? extends ClockDecl> getClockVars() {
		final Collection<ClockDecl> clockVars = new HashSet<>();
		for (final TCFA tcfa : tcfas) {
			clockVars.addAll(tcfa.getClockVars());
		}
		return Collections.unmodifiableCollection(clockVars);
	}

}
