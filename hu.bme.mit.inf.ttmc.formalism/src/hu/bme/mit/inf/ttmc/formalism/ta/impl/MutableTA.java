package hu.bme.mit.inf.ttmc.formalism.ta.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.Constrs.True;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.formalism.ta.TA;
import hu.bme.mit.inf.ttmc.formalism.ta.TAEdge;
import hu.bme.mit.inf.ttmc.formalism.ta.TALoc;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Constr;

public class MutableTA implements TA {

	final Collection<Clock> clocks;

	private final Collection<TALoc> locs;
	private final Collection<TAEdge> edges;

	private TALoc initLoc;

	public MutableTA() {
		clocks = new HashSet<>();
		locs = new HashSet<>();
		edges = new HashSet<>();
		initLoc = createLoc(True());
	}

	////////

	@Override
	public TALoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final TALoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////////

	@Override
	public Collection<? extends Clock> getClocks() {
		return Collections.unmodifiableCollection(clocks);
	}

	@Override
	public Collection<? extends TALoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	@Override
	public Collection<? extends TAEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	////////

	public void addClock(final Clock clock) {
		checkNotNull(clock);
		checkArgument(!clocks.stream().anyMatch(c -> c.getName().equals(clock.getName())));
		clocks.add(clock);
	}

	////////

	public TALoc createLoc(final Constr invar) {
		checkNotNull(invar);
		checkArgument(clocks.containsAll(invar.getClocks()));

		final TALoc loc = new MutableTALoc(invar);
		locs.add(loc);
		return loc;
	}

	////////

	public TAEdge createEdge(final TALoc source, final Constr guard, final Collection<? extends Clock> resets,
			final TALoc target) {
		checkNotNull(source);
		checkNotNull(guard);
		checkNotNull(resets);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(clocks.containsAll(guard.getClocks()));
		checkArgument(clocks.containsAll(resets));
		checkArgument(locs.contains(target));

		final TAEdge edge = new MutableTAEdge(source, guard, resets, target);
		((MutableTALoc) source).outEdges.add(edge);
		((MutableTALoc) target).inEdges.add(edge);
		edges.add(edge);
		return edge;
	}

}
