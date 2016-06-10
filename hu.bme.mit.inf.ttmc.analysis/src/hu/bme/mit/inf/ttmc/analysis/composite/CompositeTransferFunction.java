package hu.bme.mit.inf.ttmc.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;

public class CompositeTransferFunction<S1 extends State, S2 extends State, P1 extends Precision, P2 extends Precision, Trans>
		implements TransferFunction<CompositeState<S1, S2>, CompositePrecision<P1, P2>, Trans> {

	private final TransferFunction<S1, P1, Trans> transferFunction1;
	private final TransferFunction<S2, P2, Trans> transferFunction2;
	private final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator;

	public CompositeTransferFunction(final TransferFunction<S1, P1, Trans> transferFunction1,
			final TransferFunction<S2, P2, Trans> transferFunction2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		this.transferFunction1 = checkNotNull(transferFunction1);
		this.transferFunction2 = checkNotNull(transferFunction2);
		this.strenghteningOperator = checkNotNull(strenghteningOperator);
	}

	public CompositeTransferFunction(final TransferFunction<S1, P1, Trans> transferFunction1,
			final TransferFunction<S2, P2, Trans> transferFunction2) {
		this(transferFunction1, transferFunction2, (states, precision) -> states);
	}

	@Override
	public Collection<? extends CompositeState<S1, S2>> getSuccStates(final CompositeState<S1, S2> state,
			final CompositePrecision<P1, P2> precision, final Trans trans) {
		checkNotNull(state);
		checkNotNull(precision);
		checkNotNull(trans);

		final Collection<? extends S1> succStates1 = transferFunction1.getSuccStates(state._1(), precision._1(), trans);
		final Collection<? extends S2> succStates2 = transferFunction2.getSuccStates(state._2(), precision._2(), trans);
		final Collection<CompositeState<S1, S2>> compositeIniStates = CompositeState.product(succStates1, succStates2);
		return strenghteningOperator.strengthen(compositeIniStates, precision);
	}

}
