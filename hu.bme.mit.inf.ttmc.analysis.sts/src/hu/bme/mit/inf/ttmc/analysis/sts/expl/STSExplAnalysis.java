package hu.bme.mit.inf.ttmc.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplDomain;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.sts.STSAction;
import hu.bme.mit.inf.ttmc.analysis.sts.STSActionFunction;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSExplAnalysis implements Analysis<ExplState, STSAction, ExplPrecision> {

	private final ExplDomain domain;
	private final STSExplInitFunction initFunction;
	private final STSExplTransferFunction transferFunction;
	private final ActionFunction<? super ExplState, ? extends STSAction> actionFunction;

	public STSExplAnalysis(final STS sts, final Solver solver) {
		checkNotNull(sts);
		checkNotNull(solver);
		domain = ExplDomain.getInstance();
		initFunction = new STSExplInitFunction(sts, solver);
		transferFunction = new STSExplTransferFunction(sts, solver);
		actionFunction = new STSActionFunction(sts);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ExplState, STSAction, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super ExplState, ? extends STSAction> getActionFunction() {
		return actionFunction;
	}

}
