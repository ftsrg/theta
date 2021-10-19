package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.Skip;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class XcfaDeclarativeTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaDeclarativeState<S>, XcfaDeclarativeAction, XcfaDeclarativePrec<P>> {

	private final TransFunc<S, ? super XcfaDeclarativeAction, ? super P> transFunc;

	private XcfaDeclarativeTransFunc(final TransFunc<S, ? super XcfaDeclarativeAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclarativeTransFunc<S, P> create(final TransFunc<S, ? super XcfaDeclarativeAction, ? super P> transFunc) {
		return new XcfaDeclarativeTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaDeclarativeState<S>> getSuccStates(final XcfaDeclarativeState<S> state, final XcfaDeclarativeAction action, final XcfaDeclarativePrec<P> prec) {
		final List<XcfaLabel> stmts = new ArrayList<>();

		final List<XcfaLabel.StartThreadXcfaLabel> startThreadList = new ArrayList<>();
		final List<XcfaLabel.JoinThreadXcfaLabel> joinThreadList = new ArrayList<>();
		final List<XcfaLabel> memoryList = new ArrayList<>();
		Boolean atomicBegin = null;

		for (XcfaLabel label : action.getLabels()) {
			if(label instanceof XcfaLabel.StmtXcfaLabel) {
				stmts.add(label);
			} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {
				startThreadList.add((XcfaLabel.StartThreadXcfaLabel) label);
			} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {
				joinThreadList.add((XcfaLabel.JoinThreadXcfaLabel) label);
			} else if (label instanceof XcfaLabel.AtomicBeginXcfaLabel) {
				atomicBegin = true;
			} else if (label instanceof XcfaLabel.AtomicEndXcfaLabel) {
				atomicBegin = false;
			} else if (label instanceof XcfaLabel.LoadXcfaLabel) {
				memoryList.add(label);
				stmts.add(Stmt(Havoc(((XcfaLabel.LoadXcfaLabel<?>) label).getLocal())));
			} else if (label instanceof XcfaLabel.StoreXcfaLabel) {
				memoryList.add(label);
			} else if (label instanceof XcfaLabel.FenceXcfaLabel) {
				memoryList.add(label);
			} else {
				throw new UnsupportedOperationException("Could not handle label " + label);
			}
		}
		if(stmts.size() == 0) {
			stmts.add(Stmt(Skip()));
		}
		Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
		P globalPrec = prec.getGlobalPrec();
		if(globalPrec instanceof PredPrec) {
			final Set<Expr<BoolType>> preds = new LinkedHashSet<>(((PredPrec) globalPrec).getPreds());
			((PredState)state.getGlobalState()).getPreds().forEach(boolTypeExpr -> preds.add(ExprUtils.ponate(boolTypeExpr)));
			preds.addAll(state.getEqPrec());
			globalPrec = (P) PredPrec.of(preds);
		}
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), action.withLabels(stmts), globalPrec)) {
			XcfaDeclarativeState<S> st = state.atomicbegin(atomicBegin).startthreads(startThreadList).jointhreads(joinThreadList).advance(succState, action);
			Collection<XcfaDeclarativeState<S>> sts = List.of(st);
			for (XcfaLabel xcfaLabel : memoryList) {
				Collection<XcfaDeclarativeState<S>> newSts = new ArrayList<>();
				for (XcfaDeclarativeState<S> s : sts) {
					newSts.addAll(s.memory(xcfaLabel));
				}
				sts = newSts;
			}
			newStates.addAll(sts);
		}
		return newStates;
	}
}
