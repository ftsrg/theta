package hu.bme.mit.theta.analysis.zone;

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

import com.google.common.collect.Sets;

import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

final class DbmSignature implements Iterable<ClockDecl> {

	private final ArrayList<ClockDecl> indexToClock;
	private final HashMap<ClockDecl, Integer> clockToIndex;

	private DbmSignature(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);

		indexToClock = new ArrayList<>(clocks.size());
		clockToIndex = new HashMap<>(clocks.size());

		add(ZeroClock.getInstance());

		for (final ClockDecl clock : clocks) {
			if (!contains(clock)) {
				add(clock);
			}
		}
	}

	private DbmSignature(final DbmSignature signature) {
		checkNotNull(signature);
		indexToClock = new ArrayList<>(signature.indexToClock);
		clockToIndex = new HashMap<>(signature.clockToIndex);
	}

	////

	static DbmSignature over(final Collection<? extends ClockDecl> clocks) {
		return new DbmSignature(clocks);
	}

	static DbmSignature copyOf(final DbmSignature signature) {
		return new DbmSignature(signature);
	}

	////

	public static DbmSignature union(final DbmSignature signature1, final DbmSignature signature2) {
		checkNotNull(signature1);
		checkNotNull(signature2);
		final Set<ClockDecl> clocks = Sets.union(signature1.asSet(), signature2.asSet());
		return new DbmSignature(clocks);
	}

	public static DbmSignature intersection(final DbmSignature signature1, final DbmSignature signature2) {
		checkNotNull(signature1);
		checkNotNull(signature2);
		final Set<ClockDecl> clocks = Sets.intersection(signature1.asSet(), signature2.asSet());
		return new DbmSignature(clocks);
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

	public int size() {
		return indexToClock.size();
	}

	public boolean contains(final ClockDecl clock) {
		checkNotNull(clock);
		return clockToIndex.containsKey(clock);
	}

	public int indexOf(final ClockDecl clock) {
		checkArgument(contains(clock));
		return clockToIndex.get(clock);
	}

	public ClockDecl getClock(final int index) {
		checkArgument(index >= 0);
		checkArgument(index < clockToIndex.size());
		return indexToClock.get(index);
	}

	////

	private void add(final ClockDecl clock) {
		checkArgument(!contains(clock));
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
