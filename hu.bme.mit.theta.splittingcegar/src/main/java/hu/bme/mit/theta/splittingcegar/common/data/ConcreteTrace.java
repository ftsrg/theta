package hu.bme.mit.theta.splittingcegar.common.data;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Iterator;
import java.util.List;

import hu.bme.mit.theta.core.model.impl.Valuation;

public class ConcreteTrace implements Iterable<Valuation> {
	private final List<Valuation> trace;
	private final boolean isCounterexample;

	public ConcreteTrace(final List<Valuation> trace, final boolean isCounterexample) {
		this.trace = checkNotNull(trace);
		this.isCounterexample = isCounterexample;
	}

	public List<Valuation> getTrace() {
		return trace;
	}

	public Valuation getState(final int i) {
		checkArgument(0 <= i && i < size());
		return trace.get(i);
	}

	public int size() {
		return trace.size();
	}

	public boolean isCounterexample() {
		return isCounterexample;
	}

	@Override
	public Iterator<Valuation> iterator() {
		return trace.iterator();
	}
}
