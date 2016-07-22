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
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class TCFAExplAnalysis implements Analysis<ExplState, TCFAAction, ExplPrecision> {

	private final TCFAExplTransferFunction transferFunction;

	public TCFAExplAnalysis(final Solver solver) {
		checkNotNull(solver);
		transferFunction = new TCFAExplTransferFunction(solver);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return ExplDomain.getInstance();
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return TCFAExplInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ExplState, TCFAAction, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super ExplState, ? extends TCFAAction> getActionFunction() {
		throw new UnsupportedOperationException();
	}

}
