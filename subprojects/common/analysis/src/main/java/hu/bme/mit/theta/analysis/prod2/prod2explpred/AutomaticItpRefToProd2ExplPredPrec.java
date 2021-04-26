package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public final class AutomaticItpRefToProd2ExplPredPrec implements RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> {

	private final Set<VarDecl<?>> explPreferredVars;
	private final Map<VarDecl<?>, Integer> predCount;
	private final ExprSplitter exprSplitter;
	private final int maxPredCount;

	private AutomaticItpRefToProd2ExplPredPrec(final Set<VarDecl<?>> explPreferredVars, final ExprSplitter exprSplitter, final int maxPredCount) {
		this.explPreferredVars = checkNotNull(explPreferredVars);
		this.exprSplitter = checkNotNull(exprSplitter);
		this.maxPredCount = maxPredCount;

		this.predCount = new LinkedHashMap<>();
	}

	public static AutomaticItpRefToProd2ExplPredPrec create(final Set<VarDecl<?>> explPreferredVars, final ExprSplitter exprSplitter, final int maxPredCount) {
		checkArgument(maxPredCount >= 0, "MaxPredCount must be non-negative.");
		return new AutomaticItpRefToProd2ExplPredPrec(explPreferredVars, exprSplitter, maxPredCount);
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> toPrec(ItpRefutation refutation, int index) {
		final Collection<Expr<BoolType>> exprs = exprSplitter.apply(refutation.get(index));
		Set<VarDecl<?>> explSelectedVars = new LinkedHashSet<>();
		Set<Expr<BoolType>> predSelectedExprs = new LinkedHashSet<>();
		for (var expr : exprs) {
			final Set<VarDecl<?>> containedVars = ExprUtils.getVars(expr);
			boolean allExpl = true;
			for (var decl : containedVars) {
				if(maxPredCount>0){
					if (!predCount.containsKey(decl)) {
						predCount.put(decl, 1);
					}
					if(predCount.get(decl)>=maxPredCount){
						explPreferredVars.add(decl);
					} else {
						predCount.put(decl, predCount.get(decl) + 1);
					}
				}
				if(decl.getType() == Bool()){
					explPreferredVars.add(decl);
				}
				if (explPreferredVars.contains(decl)) {
					explSelectedVars.add(decl);
				} else allExpl = false;
			}
			if (!allExpl) predSelectedExprs.add(expr);
		}
		return Prod2Prec.of(ExplPrec.of(explSelectedVars), PredPrec.of(predSelectedExprs));

	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> join(Prod2Prec<ExplPrec, PredPrec> prec1, Prod2Prec<ExplPrec, PredPrec> prec2) {
		final ExplPrec joinedExpl = prec1.getPrec1().join(prec2.getPrec1());
		final PredPrec joinedPred = prec1.getPrec2().join(prec2.getPrec2());
		final var filteredPreds = joinedPred.getPreds().stream()
				.filter(pred -> !ExprUtils.getVars(pred).stream().allMatch(decl -> joinedExpl.getVars().contains(decl)))
				.collect(Collectors.toList());
		final PredPrec filteredPred = PredPrec.of(filteredPreds);
		return Prod2Prec.of(joinedExpl,filteredPred);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
