package hu.bme.mit.inf.ttmc.analysis.tcfa.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans.TCFADelayTrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans.TCFADiscreteTrans;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtUnroller;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtUnroller.StmtToExprResult;
import hu.bme.mit.inf.ttmc.formalism.utils.VarIndexes;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class TCFAPredTransferFunction implements TransferFunction<PredState, PredPrecision, TCFATrans> {

	final Solver solver;

	public TCFAPredTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<PredState> getSuccStates(final PredState state, final PredPrecision precision,
			final TCFATrans trans) {
		checkNotNull(state);
		checkNotNull(precision);
		checkNotNull(trans);

		if (trans instanceof TCFADelayTrans) {
			return Collections.singleton(state);
		} else if (trans instanceof TCFADiscreteTrans) {
			final TCFADiscreteTrans discreteTrans = (TCFADiscreteTrans) trans;
			return succStatesForDiscreteTrans(state, precision, discreteTrans);
		} else {
			throw new AssertionError();
		}
	}

	private Collection<PredState> succStatesForDiscreteTrans(final PredState state, final PredPrecision precision,
			final TCFADiscreteTrans trans) {
		checkNotNull(state);
		checkNotNull(precision);

		final ImmutableSet.Builder<PredState> builder = ImmutableSet.builder();
		solver.push();

		solver.add(PathUtils.unfold(state.toExpr(), 0));
		for (final Expr<? extends BoolType> invar : trans.getSourceDataInvars()) {
			solver.add(PathUtils.unfold(invar, 0));
		}

		final StmtToExprResult transformResult = StmtUnroller.transform(trans.getDataStmts(), VarIndexes.all(0));
		final Collection<? extends Expr<? extends BoolType>> stmtExprs = transformResult.getExprs();
		final VarIndexes indexes = transformResult.getIndexes();

		solver.add(stmtExprs);

		for (final Expr<? extends BoolType> invar : trans.getTargetDataInvars()) {
			solver.add(PathUtils.unfold(invar, indexes));
		}

		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().boolValue();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), indexes);

				final PredState nextSuccState = precision.mapToAbstractState(nextSuccStateVal);
				builder.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), indexes));
			}
		} while (moreSuccStates);
		solver.pop();

		return builder.build();
	}

}
