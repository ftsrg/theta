package hu.bme.mit.theta.formalism.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

public final class TopAnalysis<S extends State, A extends Action> implements Analysis<S, A, UnitPrec> {

	private final Collection<S> states;
	private final PartialOrd<S> partialOrd;
	private final InitFunc<S, UnitPrec> initFunc;
	private final TransFunc<S, A, UnitPrec> transFunc;

	private TopAnalysis(final S top, final PartialOrd<S> partialOrd) {
		states = ImmutableSet.of(checkNotNull(top));
		this.partialOrd = checkNotNull(partialOrd);
		this.initFunc = u -> states;
		this.transFunc = (s, u, a) -> states;
	}

	public static <S extends State, A extends Action> TopAnalysis<S, A> create(final S top,
			final PartialOrd<S> partialOrd) {
		return new TopAnalysis<>(top, partialOrd);
	}

	@Override
	public PartialOrd<S> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<S, UnitPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<S, A, UnitPrec> getTransFunc() {
		return transFunc;
	}

}
