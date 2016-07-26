package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

class DBMSignature implements Iterable<ClockDecl> {

	private final ArrayList<ClockDecl> indexToClock;
	private final HashMap<ClockDecl, Integer> clockToIndex;

	DBMSignature(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);

		indexToClock = new ArrayList<>(clocks.size());
		clockToIndex = new HashMap<>(clocks.size());

		add(ZeroClock.getInstance());

		for (final ClockDecl clock : clocks) {
			if (!isDefined(clock)) {
				add(clock);
			}
		}
	}

	DBMSignature(final DBMSignature signature) {
		checkNotNull(signature);
		indexToClock = new ArrayList<>(signature.indexToClock);
		clockToIndex = new HashMap<>(signature.clockToIndex);
	}

	////

	public List<ClockDecl> asList() {
		return Collections.unmodifiableList(indexToClock);
	}

	public Set<ClockDecl> asSet() {
		return Collections.unmodifiableSet(clockToIndex.keySet());
	}

	@Override
	public Iterator<ClockDecl> iterator() {
		return indexToClock.iterator();
	}

	////

	public boolean isDefined(final ClockDecl clock) {
		checkNotNull(clock);
		return clockToIndex.containsKey(clock);
	}

	public int size() {
		return indexToClock.size();
	}

	public int indexOf(final ClockDecl clock) {
		checkArgument(isDefined(clock));
		return clockToIndex.get(clock);
	}

	public ClockDecl getClock(final int index) {
		checkArgument(index >= 0);
		checkArgument(index < clockToIndex.size());
		return indexToClock.get(index);
	}

	////

	private void add(final ClockDecl clock) {
		checkArgument(!isDefined(clock));
		indexToClock.add(clock);
		clockToIndex.put(clock, clockToIndex.size());
	}

	////

	@Override
	public String toString() {
		final StringJoiner joiner = new StringJoiner(", ", "DBMSignature(", ")");
		for (final ClockDecl clock : asList()) {
			joiner.add(clock.toString());
		}
		return joiner.toString();
	}

}
