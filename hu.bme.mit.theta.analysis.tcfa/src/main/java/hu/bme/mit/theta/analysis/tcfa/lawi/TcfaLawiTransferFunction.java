package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.expl.TcfaExplTransferFunction;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.solver.Solver;

final class TcfaLawiTransferFunction implements TransferFunction<TcfaLawiState, TcfaAction, NullPrecision> {

	@SuppressWarnings("unused")
	private final ExplPrecision precision;
	@SuppressWarnings("unused")
	private final TransferFunction<ExplState, TcfaAction, ExplPrecision> transferFunction;

	TcfaLawiTransferFunction(final TCFA tcfa, final Solver solver) {
		checkNotNull(tcfa);
		precision = ExplPrecision.create(tcfa.getDataVars());
		transferFunction = TcfaExplTransferFunction.create(solver);
	}

	@Override
	public Collection<? extends TcfaLawiState> getSuccStates(final TcfaLawiState state, final TcfaAction action,
			final NullPrecision precision) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
