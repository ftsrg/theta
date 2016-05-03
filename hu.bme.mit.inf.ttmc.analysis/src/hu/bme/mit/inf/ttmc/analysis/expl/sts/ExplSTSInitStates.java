package hu.bme.mit.inf.ttmc.analysis.expl.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.InitStates;
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

public class ExplSTSInitStates implements InitStates<ExplState, ExplPrecision> {

	private final Solver solver;
	private final STS sts;

	public ExplSTSInitStates(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends ExplState> get(final ExplPrecision precision) {
		final Set<ExplState> initStates = new HashSet<>();
		boolean moreInitialStates;

		do {
			AndExpr nextInitStateExpr = null;
			solver.push();
			solver.add(sts.unrollInit(0));
			solver.add(sts.unrollInv(0));
			for (final ExplState existingInit : initStates)
				solver.add(sts.unroll(Exprs.Not(existingInit.asExpr()), 0));

			moreInitialStates = solver.check().boolValue();
			if (moreInitialStates) {
				nextInitStateExpr = sts.getConcreteState(solver.getModel(), 0, precision.getVisibleVars());
			}
			solver.pop();

			if (moreInitialStates) {
				final Map<VarDecl<? extends Type>, LitExpr<? extends Type>> nextInitStateValues = new HashMap<>();
				for (final Expr<? extends BoolType> expr : nextInitStateExpr.getOps()) {
					// TODO: replace when there is an interface for concrete states
					assert (expr instanceof EqExpr);
					final EqExpr eq = (EqExpr) expr;
					assert (eq.getLeftOp() instanceof VarRefExpr<?>);
					assert (eq.getRightOp() instanceof LitExpr<?>);
					nextInitStateValues.put(((VarRefExpr<? extends Type>) eq.getLeftOp()).getDecl(), (LitExpr<? extends Type>) eq.getRightOp());
				}
				initStates.add(ExplState.create(nextInitStateValues));
			}

		} while (moreInitialStates);

		return initStates;
	}

}
