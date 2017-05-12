package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public final class XtaState<S extends State> implements State {
	private static final int HASH_SEED = 8291;
	private volatile int hashCode = 0;

	private final List<Loc> locs;
	private final Valuation val;
	private final S state;

	public XtaState(final List<Loc> locs, final Valuation val, final S state) {
		this.locs = ImmutableList.copyOf(checkNotNull(locs));
		this.val = checkNotNull(val);
		this.state = checkNotNull(state);
	}

	public static <S extends State> XtaState<S> of(final List<Loc> locs, final Valuation val, final S state) {
		return new XtaState<>(locs, val, state);
	}

	public static <S extends State> Collection<XtaState<S>> collectionOf(final List<Loc> locs, final Valuation val,
			final Collection<? extends S> states) {
		final Collection<XtaState<S>> result = new ArrayList<>();
		for (final S state : states) {
			final XtaState<S> initXtaState = XtaState.of(locs, val, state);
			result.add(initXtaState);
		}
		return result;
	}

	public List<Loc> getLocs() {
		return locs;
	}

	public Valuation getVal() {
		return val;
	}

	public S getState() {
		return state;
	}

	public <S2 extends State> XtaState<S2> withState(final S2 state) {
		return XtaState.of(this.locs, this.val, state);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + locs.hashCode();
			result = 31 * result + val.hashCode();
			result = 31 * result + state.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XtaState) {
			final XtaState<?> that = (XtaState<?>) obj;
			return this.locs.equals(that.locs) && this.val.equals(that.val) && this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner("\n");
		locs.forEach(l -> sj.add(l.getName()));
		val.getDecls().forEach(d -> sj.add(d.getName() + " = " + val.eval(d).get()));
		locs.forEach(l -> l.getInvars().forEach(i -> sj.add("[" + i + "]")));
		sj.add(state.toString());
		return sj.toString();
	}
}
