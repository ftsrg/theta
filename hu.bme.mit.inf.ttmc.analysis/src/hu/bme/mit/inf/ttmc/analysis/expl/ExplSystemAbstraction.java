package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.SystemAbstraction;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;

public class ExplSystemAbstraction implements SystemAbstraction<ExplState, ExplPrecision> {

	private final InitFunction<ExplState, ExplPrecision> initFunction;
	private final TransferFunction<ExplState, ExplPrecision> transferFunction;

	ExplSystemAbstraction(final SolverManager manager, final Expr<? extends BoolType> init,
			final Expr<? extends BoolType> trans) {
		checkNotNull(manager);
		checkNotNull(init);
		checkNotNull(trans);
		final Solver solver = manager.createSolver(true, true);
		initFunction = new ExplInitFunction(solver, init);
		transferFunction = new ExplTransferFunction(solver, trans);
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ExplState, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

}
