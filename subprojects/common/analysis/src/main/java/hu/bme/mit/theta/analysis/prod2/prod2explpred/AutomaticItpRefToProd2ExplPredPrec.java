package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.common.logging.Logger;
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
	private final Map<VarDecl<?>, Set<Expr<BoolType>>> atomCount;
	private final ExprSplitter exprSplitter;
	private final int maxAtomCount;

	private AutomaticItpRefToProd2ExplPredPrec(final Set<VarDecl<?>> explPreferredVars, final ExprSplitter exprSplitter, final int maxAtomCount) {
		this.explPreferredVars = checkNotNull(explPreferredVars);
		this.exprSplitter = checkNotNull(exprSplitter);
		this.maxAtomCount = maxAtomCount;

		this.atomCount = new LinkedHashMap<>();
	}

	public static AutomaticItpRefToProd2ExplPredPrec create(final Set<VarDecl<?>> explPreferredVars, final ExprSplitter exprSplitter, final int maxAtomCount) {
		checkArgument(maxAtomCount >= 0, "MaxPredCount must be non-negative.");
		return new AutomaticItpRefToProd2ExplPredPrec(explPreferredVars, exprSplitter, maxAtomCount);
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> toPrec(ItpRefutation refutation, int index) {
		final Expr<BoolType> refExpr = refutation.get(index);

		final var canonicalAtoms = ExprUtils.getAtoms(refExpr).stream()
				.map(ExprUtils::canonize)
				.collect(Collectors.toSet());
		canonicalAtoms.forEach(
				atom -> ExprUtils.getVars(atom).forEach(
						decl -> atomCount.computeIfAbsent(decl,(k) -> new HashSet<Expr<BoolType>>()).add(atom)
				)
		);

		explPreferredVars.addAll(
				ExprUtils.getVars(refExpr).stream()
					.filter(decl -> atomCount.get(decl).size() >= maxAtomCount && maxAtomCount != 0 || decl.getType() == Bool())
					.collect(Collectors.toSet()));

		final var explSelectedVars = ExprUtils.getVars(refExpr).stream()
				.filter(explPreferredVars::contains)
				.collect(Collectors.toSet());
		final var predSelectedExprs = exprSplitter.apply(refExpr).stream()
				.filter(expr -> !explPreferredVars.containsAll(ExprUtils.getVars(expr)))
				.collect(Collectors.toSet());

		return Prod2Prec.of(ExplPrec.of(explSelectedVars), PredPrec.of(predSelectedExprs));
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> join(Prod2Prec<ExplPrec, PredPrec> prec1, Prod2Prec<ExplPrec, PredPrec> prec2) {
		final ExplPrec joinedExpl = prec1.getPrec1().join(prec2.getPrec1());
		final PredPrec joinedPred = prec1.getPrec2().join(prec2.getPrec2());
		final var filteredPreds = joinedPred.getPreds().stream()
				.filter(pred -> !joinedExpl.getVars().containsAll(ExprUtils.getVars(pred)))
				.collect(Collectors.toList());
		final PredPrec filteredPred = PredPrec.of(filteredPreds);
		return Prod2Prec.of(joinedExpl,filteredPred);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
