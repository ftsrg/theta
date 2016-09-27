package hu.bme.mit.theta.formalism.tcfa;

import static java.util.stream.Collectors.toList;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public final class NetworkTcfa implements TCFA {

	private final TcfaLoc initLoc;

	private final Collection<VarDecl<?>> dataVars;
	private final Collection<ClockDecl> clockVars;

	private NetworkTcfa(final List<? extends TCFA> tcfas) {
		initLoc = new NetworkTcfaLoc(getInitLocs(tcfas));
		dataVars = extractDataVars(tcfas);
		clockVars = extractClockVars(tcfas);
	}

	private static List<TcfaLoc> getInitLocs(final List<? extends TCFA> tcfas) {
		return tcfas.stream().map(TCFA::getInitLoc).collect(toList());
	}

	private static Collection<VarDecl<?>> extractDataVars(final List<? extends TCFA> tcfas) {
		final ImmutableSet.Builder<VarDecl<?>> builder = ImmutableSet.builder();
		for (final TCFA tcfa : tcfas) {
			builder.addAll(tcfa.getDataVars());
		}
		return builder.build();
	}

	private static Collection<ClockDecl> extractClockVars(final List<? extends TCFA> tcfas) {
		final ImmutableSet.Builder<ClockDecl> builder = ImmutableSet.builder();
		for (final TCFA tcfa : tcfas) {
			builder.addAll(tcfa.getClockVars());
		}
		return builder.build();
	}

	public static NetworkTcfa of(final List<? extends TCFA> tcfas) {
		return new NetworkTcfa(tcfas);
	}

	public static NetworkTcfa of(final TCFA... tcfas) {
		return of(Arrays.asList(tcfas));
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
	public Collection<VarDecl<?>> getDataVars() {
		return dataVars;
	}

	@Override
	public Collection<ClockDecl> getClockVars() {
		return clockVars;
	}

}
