package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Predicate;

import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFALocTargetPredicate implements TargetPredicate<TCFAState<?>> {

	private final Predicate<? super TCFALoc> predicate;

	public TCFALocTargetPredicate(final Predicate<? super TCFALoc> predicate) {
		this.predicate = checkNotNull(predicate);
	}

	@Override
	public boolean isTargetState(final TCFAState<?> state) {
		return predicate.test(state.getLoc());
	}

}
