package hu.bme.mit.inf.ttmc.analysis.pred.precisions;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public final class TreePredPrecision implements PredPrecision {

	private final Node root;

	public static TreePredPrecision create(final Collection<? extends Expr<? extends BoolType>> preds) {
		return new TreePredPrecision(preds);
	}

	private TreePredPrecision(final Collection<? extends Expr<? extends BoolType>> preds) {
		checkNotNull(preds);

		final Set<Expr<? extends BoolType>> ponatedPreds = new HashSet<>();
		for (final Expr<? extends BoolType> pred : preds) {
			ponatedPreds.add(ExprUtils.ponate(pred));
		}

		if (ponatedPreds.size() == 0) {
			ponatedPreds.add(Exprs.True());
		}

		root = new Node(new ArrayList<>(ponatedPreds));
	}

	private final static class Node {
		private final Expr<? extends BoolType> ponPred;
		private final Expr<? extends BoolType> negPred;

		private Optional<Node> ponRefined;
		private Optional<Node> negRefined;

		public Node(final Expr<? extends BoolType> pred) {
			this(Collections.singletonList(pred));
		}

		public Node(final List<? extends Expr<? extends BoolType>> preds) {
			assert preds.size() > 0;
			assert !(preds.get(0) instanceof NotExpr);
			this.ponPred = preds.get(0);
			this.negPred = Exprs.Not(this.ponPred);
			if (preds.size() == 1) {
				this.ponRefined = Optional.empty();
				this.negRefined = Optional.empty();
			} else {
				this.ponRefined = Optional.of(new Node(preds.subList(1, preds.size())));
				this.negRefined = Optional.of(new Node(preds.subList(1, preds.size())));
			}
		}

		public Expr<? extends BoolType> getPonPred() {
			return ponPred;
		}

		public Expr<? extends BoolType> getNegPred() {
			return negPred;
		}

		public void refinePon(final Expr<? extends BoolType> pred) {
			assert !ponRefined.isPresent();
			ponRefined = Optional.of(new Node(pred));
		}

		public void refineNeg(final Expr<? extends BoolType> pred) {
			assert !negRefined.isPresent();
			negRefined = Optional.of(new Node(pred));
		}

		public Optional<Node> getPonRefined() {
			return ponRefined;
		}

		public Optional<Node> getNegRefined() {
			return negRefined;
		}
	}

	@Override
	public PredState mapToAbstractState(final Valuation valuation) {
		checkNotNull(valuation);
		final Set<Expr<? extends BoolType>> statePreds = new HashSet<>();

		Node node = root;

		while (node != null) {
			final LitExpr<? extends BoolType> predHolds = FormalismUtils.evaluate(node.getPonPred(), valuation);
			if (predHolds.equals(Exprs.True())) {
				statePreds.add(node.getPonPred());
				node = node.getPonRefined().isPresent() ? node.getPonRefined().get() : null;
			} else {
				statePreds.add(node.getNegPred());
				node = node.getNegRefined().isPresent() ? node.getNegRefined().get() : null;
			}
		}

		return PredState.create(statePreds);
	}

	public void refine(final PredState state, final Expr<? extends BoolType> pred) {
		checkNotNull(state);
		checkNotNull(pred);

		final Expr<? extends BoolType> refiningPred = ExprUtils.ponate(pred);

		Node node = root;
		while (node != null) {
			if (state.getPreds().contains(node.getPonPred())) {
				if (node.getPonRefined().isPresent()) {
					node = node.getPonRefined().get();
				} else {
					node.refinePon(refiningPred);
					node = null;
				}
			} else if (state.getPreds().contains(node.getNegPred())) {
				if (node.getNegRefined().isPresent()) {
					node = node.getNegRefined().get();
				} else {
					node.refineNeg(refiningPred);
					node = null;
				}
			}
		}
	}
}
