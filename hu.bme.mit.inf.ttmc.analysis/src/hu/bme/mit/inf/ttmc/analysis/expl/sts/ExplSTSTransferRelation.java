package hu.bme.mit.inf.ttmc.analysis.expl.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class ExplSTSTransferRelation implements TransferRelation<ExplState, ExplPrecision> {

	private final Solver solver;
	private final STS sts;

	public ExplSTSTransferRelation(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExplPrecision precision) {
		checkNotNull(state);
		final Set<ExplState> succStates = new HashSet<>();
		boolean moreSuccessors;
		do {
			AndExpr nextSuccExpr = null;
			solver.push();
			solver.add(sts.unroll(state.asExpr(), 0));
			solver.add(sts.unrollInv(0));
			solver.add(sts.unrollInv(1));
			solver.add(sts.unrollTrans(0));
			for (final ExplState existingSucc : succStates)
				solver.add(sts.unroll(Exprs.Not(existingSucc.asExpr()), 1));

			moreSuccessors = solver.check().boolValue();
			if (moreSuccessors)
				nextSuccExpr = sts.getConcreteState(solver.getModel(), 1, precision.getVisibleVars());

			solver.pop();
			if (moreSuccessors) {
				final Map<VarDecl<? extends Type>, LitExpr<? extends Type>> nextSuccValues = new HashMap<>();
				for (final Expr<? extends BoolType> expr : nextSuccExpr.getOps()) {
					assert (expr instanceof EqExpr);
					final EqExpr eq = (EqExpr) expr;
					assert (eq.getLeftOp() instanceof VarRefExpr<?>);
					assert (eq.getRightOp() instanceof LitExpr<?>);
					nextSuccValues.put(((VarRefExpr<? extends Type>) eq.getLeftOp()).getDecl(), (LitExpr<? extends Type>) eq.getRightOp());
				}
				succStates.add(ExplState.create(nextSuccValues));

			}

		} while (moreSuccessors);

		return succStates;
	}
}
