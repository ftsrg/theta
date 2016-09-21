package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.ExprState;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.ConcretizerOp;
import hu.bme.mit.theta.analysis.algorithm.cegar.CounterexampleStatus;
import hu.bme.mit.theta.analysis.algorithm.cegar.ItpRefutation;
import hu.bme.mit.theta.analysis.algorithm.cegar.ItpRefutationImpl;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.TraceImpl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;

public class StsExprSeqConcretizer implements ConcretizerOp<ExprState, StsAction, ExplState, ItpRefutation> {

	private final STS sts;
	private final ItpSolver solver;
	private final Expr<? extends BoolType> negProp;

	private Optional<Trace<ExplState, StsAction>> concreteCex;
	private Optional<ItpRefutation> refutation;

	public StsExprSeqConcretizer(final STS sts, final ItpSolver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
		this.negProp = Exprs.Not(checkNotNull(sts.getProp()));
		this.concreteCex = Optional.empty();
		this.refutation = Optional.empty();
	}

	@Override
	public CounterexampleStatus concretize(final Trace<? extends ExprState, StsAction> counterexample) {
		checkNotNull(counterexample);
		checkArgument(counterexample.length() > 0);
		concreteCex = Optional.empty();
		refutation = Optional.empty();

		final List<ItpMarker> markers = new ArrayList<>(counterexample.length() + 1);
		for (int i = 0; i < counterexample.length() + 1; ++i) {
			markers.add(solver.createMarker());
		}

		final ItpPattern pattern = solver.createSeqPattern(markers);

		solver.push();
		solver.add(markers.get(0), sts.unrollInit(0));
		for (int i = 0; i < counterexample.length(); ++i) {
			solver.add(markers.get(i), sts.unrollInv(i));
			solver.add(markers.get(i), sts.unroll(counterexample.getState(i).toExpr(), i));
			if (i > 0) {
				solver.add(markers.get(i), sts.unrollTrans(i - 1));
			}
		}
		solver.add(markers.get(counterexample.length()), sts.unroll(negProp, counterexample.length() - 1));

		final boolean concretizable = solver.check().boolValue();

		if (concretizable) {
			final List<Valuation> trace = sts.extractTrace(solver.getModel(), counterexample.length());
			final List<ExplState> explStateTrace = trace.stream().map(s -> ExplState.create(s))
					.collect(Collectors.toList());
			concreteCex = Optional.of(new TraceImpl<>(explStateTrace, counterexample.getActions()));
		} else {
			final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
			for (int i = 0; i < markers.size() - 1; ++i) {
				interpolants.add(sts.foldin(solver.getInterpolant(pattern).eval(markers.get(i)), i));
				refutation = Optional.of(ItpRefutationImpl.createSequence(interpolants));
			}
		}

		solver.pop();

		return getStatus();
	}

	@Override
	public CounterexampleStatus getStatus() {
		if (concreteCex.isPresent()) {
			assert (!refutation.isPresent());
			return CounterexampleStatus.CONCRETE;
		} else if (refutation.isPresent()) {
			assert (!concreteCex.isPresent());
			return CounterexampleStatus.SPURIOUS;
		} else {
			throw new IllegalStateException("No counterexample or refutation is present!");
		}
	}

	@Override
	public Trace<ExplState, StsAction> getConcreteCounterexample() {
		checkState(getStatus() == CounterexampleStatus.CONCRETE);
		assert (concreteCex.isPresent());
		return concreteCex.get();
	}

	@Override
	public ItpRefutation getRefutation() {
		checkState(getStatus() == CounterexampleStatus.SPURIOUS);
		assert (refutation.isPresent());
		return refutation.get();
	}

}
