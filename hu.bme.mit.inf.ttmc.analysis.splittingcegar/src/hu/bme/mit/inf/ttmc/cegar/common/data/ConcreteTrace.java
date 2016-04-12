package hu.bme.mit.inf.ttmc.cegar.common.data;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Iterator;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public class ConcreteTrace implements Iterable<AndExpr> {
	private final List<AndExpr> trace;
	private final boolean isCounterexample;

	public ConcreteTrace(final List<AndExpr> trace, final boolean isCounterexample) {
		this.trace = checkNotNull(trace);
		this.isCounterexample = isCounterexample;
	}

	public List<AndExpr> getTrace() {
		return trace;
	}

	public Expr<? extends Type> getState(final int i) {
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
	public Iterator<AndExpr> iterator() {
		return trace.iterator();
	}
}
