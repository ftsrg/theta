package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.cat.MemoryModelChecker;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;

public class XcfaDeclarativeChecker<R extends Refutation> implements ExprTraceChecker<R> {
	private final ExprTraceChecker<R> traceChecker;

	private XcfaDeclarativeChecker(final ExprTraceChecker<R> traceChecker) {
		this.traceChecker = traceChecker;
	}

	public static <R extends Refutation> XcfaDeclarativeChecker<R> create(final ExprTraceChecker<R> traceChecker) {
		return new XcfaDeclarativeChecker<R>(traceChecker);
	}

	@Override
	public ExprTraceStatus<R> check(Trace<? extends ExprState, ? extends ExprAction> trace) {
		MemoryModelChecker.Builder model = MemoryModelChecker.builder();
		String w1 = "w1";
		String w2 = "w2";
		String r1 = "r1";
		String r2 = "r2";
		model.addUnaryFact("W", w1);
		model.addUnaryFact("W", w2);
		model.addUnaryFact("R", r1);
		model.addUnaryFact("R", r2);
		model.addBinaryFact("poRaw", w1, w2);
		model.addBinaryFact("poRaw", r1, r2);
		model.addBinaryFact("locRaw", w1, w2);
		model.addBinaryFact("locRaw", r1, r2);
		model.addBinaryFact("locRaw", r1, w1);
		model.addBinaryFact("intRaw", r1, r2);
		model.addBinaryFact("intRaw", w1, w2);
		model.build().printRf();


		final List<XcfaDeclarativeAction> newActions = new ArrayList<>();
		for (ExprAction action : trace.getActions()) {
			checkState(action instanceof XcfaDeclarativeAction, "Wrong type for XcfaDeclarativeChecker!");
			XcfaDeclarativeAction xcfaAction = (XcfaDeclarativeAction) action;
			if(xcfaAction instanceof XcfaDeclarativeAction.XcfaDeclarativeThreadChangeAction) {
				newActions.add(xcfaAction);
			} else {
				final List<XcfaLabel> newLabels = new ArrayList<>();
				for (XcfaLabel label : xcfaAction.getLabels()) {
					if(label instanceof XcfaLabel.StoreXcfaLabel<?>) {

					} else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {

					} else if (label instanceof XcfaLabel.FenceXcfaLabel) {

					} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {

					} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {

					} else if (label instanceof XcfaLabel.AtomicBeginXcfaLabel) {

					} else if (label instanceof XcfaLabel.AtomicEndXcfaLabel) {

					} else {
						newLabels.add(label);
					}
				}
				newActions.add(XcfaDeclarativeAction.create(XcfaEdge.of(xcfaAction.getSource(), xcfaAction.getTarget(), newLabels)));
			}
		}
		return traceChecker.check(Trace.of(trace.getStates(), newActions));
	}
}
