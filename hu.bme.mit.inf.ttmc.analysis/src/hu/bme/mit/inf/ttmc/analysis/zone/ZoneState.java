package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ImmutableSortedMap;
import com.google.common.collect.ImmutableSortedSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public final class ZoneState {

	private final Map<ClockDecl, Integer> clockToIndex;
	private final DBM dbm;

	private ZoneState(final Map<ClockDecl, Integer> clockToIndex, final DBM dbm) {
		this.clockToIndex = clockToIndex;
		this.dbm = dbm;
	}

	public static ZoneState zero(final Collection<? extends ClockDecl> clockDecls) {

		final Map<ClockDecl, Integer> clockToIndex = toIndexMap(clockDecls);
		return new ZoneState(clockToIndex, DBM.zero(clockDecls.size()));
	}

	public static ZoneState top(final Collection<? extends ClockDecl> clockDecls) {
		final Map<ClockDecl, Integer> clockToIndex = toIndexMap(clockDecls);
		return new ZoneState(clockToIndex, DBM.top(clockDecls.size()));
	}

	////////

	public ZoneState up() {
		final DBM dbm = DBM.copyOf(this.dbm);
		dbm.up();
		return new ZoneState(clockToIndex, dbm);
	}

	public ZoneState down() {
		final DBM dbm = DBM.copyOf(this.dbm);
		dbm.down();
		return new ZoneState(clockToIndex, dbm);
	}

	////////

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(String.format("%-12s", ""));
		for (final ClockDecl clockDecl : clockToIndex.keySet()) {
			sb.append(String.format("%-12s", clockDecl.getName()));
		}
		sb.append(System.lineSeparator());
		sb.append(dbm);
		return sb.toString();
	}

	////////

	private static Map<ClockDecl, Integer> toIndexMap(final Collection<? extends ClockDecl> clockDecls) {
		final Set<ClockDecl> sortedClockDecls = ImmutableSortedSet.<ClockDecl> naturalOrder().addAll(clockDecls)
				.build();
		final ImmutableSortedMap.Builder<ClockDecl, Integer> builder = ImmutableSortedMap.naturalOrder();

		int i = 1;
		for (final ClockDecl clockDecl : sortedClockDecls) {
			builder.put(clockDecl, i);
			i++;
		}
		return builder.build();

	}

}
