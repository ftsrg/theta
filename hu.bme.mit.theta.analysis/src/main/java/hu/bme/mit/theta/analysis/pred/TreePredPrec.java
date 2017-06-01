package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

public final class TreePredPrec implements PredPrec {

	private final Node root;

	public static TreePredPrec create(final Iterable<? extends Expr<BoolType>> preds) {
		return new TreePredPrec(preds);
	}

	private TreePredPrec(final Iterable<? extends Expr<BoolType>> preds) {
		checkNotNull(preds);

		final Set<Expr<BoolType>> ponatedPreds = new HashSet<>();
		for (final Expr<BoolType> pred : preds) {
			ponatedPreds.add(ExprUtils.ponate(pred));
		}

		if (ponatedPreds.isEmpty()) {
			ponatedPreds.add(True());
		}

		root = new Node(new ArrayList<>(ponatedPreds));
	}

	private final static class Node {
		private final Expr<BoolType> ponPred;
		private final Expr<BoolType> negPred;

		private Optional<Node> ponRefined;
		private Optional<Node> negRefined;

		public Node(final Expr<BoolType> pred) {
			this(Collections.singletonList(pred));
		}

		public Node(final List<? extends Expr<BoolType>> preds) {
			assert !preds.isEmpty();
			assert !(preds.get(0) instanceof NotExpr);
			this.ponPred = preds.get(0);
			this.negPred = Not(this.ponPred);
			if (preds.size() == 1) {
				this.ponRefined = Optional.empty();
				this.negRefined = Optional.empty();
			} else {
				this.ponRefined = Optional.of(new Node(preds.subList(1, preds.size())));
				this.negRefined = Optional.of(new Node(preds.subList(1, preds.size())));
			}
		}

		public Expr<BoolType> getPonPred() {
			return ponPred;
		}

		public Expr<BoolType> getNegPred() {
			return negPred;
		}

		public void refinePon(final Expr<BoolType> pred) {
			assert !ponRefined.isPresent();
			ponRefined = Optional.of(new Node(pred));
		}

		public void refineNeg(final Expr<BoolType> pred) {
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
	public PredState createState(final Valuation valuation) {
		checkNotNull(valuation);
		final Set<Expr<BoolType>> statePreds = new HashSet<>();

		Node node = root;

		while (node != null) {
			final LitExpr<BoolType> predHolds = ExprUtils.evaluate(node.getPonPred(), valuation);
			if (predHolds.equals(True())) {
				statePreds.add(node.getPonPred());
				node = node.getPonRefined().isPresent() ? node.getPonRefined().get() : null;
			} else {
				statePreds.add(node.getNegPred());
				node = node.getNegRefined().isPresent() ? node.getNegRefined().get() : null;
			}
		}

		return PredState.of(statePreds);
	}

	public void refine(final PredState state, final Expr<BoolType> pred) {
		checkNotNull(state);
		checkNotNull(pred);

		final Expr<BoolType> refiningPred = ExprUtils.ponate(pred);

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
			} else {
				throw new IllegalStateException(
						String.format("State %s contains neither %s nor its negation!", state, pred));
			}
		}
	}
}
