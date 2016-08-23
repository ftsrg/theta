package hu.bme.mit.inf.ttmc.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplDomain;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class TcfaExplAnalysis implements Analysis<ExplState, TcfaAction, ExplPrecision> {

	private final TcfaExplTransferFunction transferFunction;

	public TcfaExplAnalysis(final Solver solver) {
		checkNotNull(solver);
		transferFunction = new TcfaExplTransferFunction(solver);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return ExplDomain.getInstance();
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return TcfaExplInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ExplState, TcfaAction, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super ExplState, ? extends TcfaAction> getActionFunction() {
		throw new UnsupportedOperationException();
	}

}
