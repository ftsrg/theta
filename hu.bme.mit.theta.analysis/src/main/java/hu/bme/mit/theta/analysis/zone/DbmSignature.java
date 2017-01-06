package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

final class DbmSignature implements Iterable<ClockDecl> {

	private final List<ClockDecl> indexToClock;
	private final Map<ClockDecl, Integer> clockToIndex;

	private DbmSignature(final Iterable<? extends ClockDecl> clocks) {
		checkNotNull(clocks);

		final ImmutableList.Builder<ClockDecl> indexToClockBuilder = ImmutableList.builder();
		final ImmutableMap.Builder<ClockDecl, Integer> clockToIndexBuilder = ImmutableMap.builder();

		final Set<ClockDecl> addedClocks = new HashSet<>();

		indexToClockBuilder.add(ZeroClock.getInstance());
		clockToIndexBuilder.put(ZeroClock.getInstance(), addedClocks.size());
		addedClocks.add(ZeroClock.getInstance());

		for (final ClockDecl clock : clocks) {
			if (!addedClocks.contains(clock)) {
				indexToClockBuilder.add(clock);
				clockToIndexBuilder.put(clock, addedClocks.size());
				addedClocks.add(clock);
			}
		}

		indexToClock = indexToClockBuilder.build();
		clockToIndex = clockToIndexBuilder.build();
	}

	////

	static DbmSignature over(final Iterable<? extends ClockDecl> clocks) {
		return new DbmSignature(clocks);
	}

	public static DbmSignature union(final DbmSignature signature1, final DbmSignature signature2) {
		checkNotNull(signature1);
		checkNotNull(signature2);
		final Iterable<ClockDecl> clocks = Sets.union(signature1.toSet(), signature2.toSet());
		return new DbmSignature(clocks);
	}

	public static DbmSignature intersection(final DbmSignature signature1, final DbmSignature signature2) {
		checkNotNull(signature1);
		checkNotNull(signature2);
		final Set<ClockDecl> clocks = Sets.intersection(signature1.toSet(), signature2.toSet());
		return new DbmSignature(clocks);
	}

	////

	public List<ClockDecl> toList() {
		return indexToClock;
	}

	public Set<ClockDecl> toSet() {
		return clockToIndex.keySet();
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

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(indexToClock).toString();
	}

	////

}
