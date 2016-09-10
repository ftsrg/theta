package hu.bme.mit.theta.formalism.ta.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.True;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.TA;
import hu.bme.mit.theta.formalism.ta.TaEdge;
import hu.bme.mit.theta.formalism.ta.TaLoc;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;

public class MutableTa implements TA {

	final Collection<ClockDecl> clocks;

	private final Collection<TaLoc> locs;
	private final Collection<TaEdge> edges;

	private TaLoc initLoc;

	public MutableTa() {
		clocks = new HashSet<>();
		locs = new HashSet<>();
		edges = new HashSet<>();
		initLoc = createLoc(True());
	}

	////////

	@Override
	public TaLoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final TaLoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////////

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return Collections.unmodifiableCollection(clocks);
	}

	@Override
	public Collection<? extends TaLoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	@Override
	public Collection<? extends TaEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	////////

	public void addClock(final ClockDecl clock) {
		checkNotNull(clock);
		checkArgument(!clocks.stream().anyMatch(c -> c.getName().equals(clock.getName())));
		clocks.add(clock);
	}

	////////

	public TaLoc createLoc(final ClockConstr invar) {
		checkNotNull(invar);
		checkArgument(clocks.containsAll(invar.getClocks()));

		final TaLoc loc = new MutableTaLoc(invar);
		locs.add(loc);
		return loc;
	}

	////////

	public TaEdge createEdge(final TaLoc source, final ClockConstr guard, final Collection<? extends ClockDecl> resets,
			final TaLoc target) {
		checkNotNull(source);
		checkNotNull(guard);
		checkNotNull(resets);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(clocks.containsAll(guard.getClocks()));
		checkArgument(clocks.containsAll(resets));
		checkArgument(locs.contains(target));

		final TaEdge edge = new MutableTaEdge(source, guard, resets, target);
		((MutableTaLoc) source).outEdges.add(edge);
		((MutableTaLoc) target).inEdges.add(edge);
		edges.add(edge);
		return edge;
	}

}
