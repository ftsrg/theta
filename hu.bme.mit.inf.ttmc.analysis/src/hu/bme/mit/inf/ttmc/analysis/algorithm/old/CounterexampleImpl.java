package hu.bme.mit.inf.ttmc.analysis.algorithm.old;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import hu.bme.mit.inf.ttmc.analysis.State;

public class CounterexampleImpl<S extends State> implements Counterexample<S> {

	private final List<S> path;

	private CounterexampleImpl(final List<? extends S> path) {
		checkNotNull(path);
		checkArgument(path.size() > 0);
		this.path = Collections.unmodifiableList(path);
	}

	public static <S extends State> CounterexampleImpl<S> create(final List<? extends S> states) {
		return new CounterexampleImpl<>(states);
	}

	@Override
	public Iterator<S> iterator() {
		return path.iterator();
	}

	@Override
	public int size() {
		return path.size();
	}

	@Override
	public S get(final int i) {
		checkArgument(0 <= i);
		checkArgument(i < size());
		return path.get(i);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Counterexample(");
		for (int i = 0; i < size(); ++i) {
			sb.append(get(i).toString());
			if (i < size() - 1)
				sb.append("; ");
		}
		sb.append(")");
		return sb.toString();
	}

}
