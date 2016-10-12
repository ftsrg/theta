package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.CexStatus;
import hu.bme.mit.theta.analysis.algorithm.cegar.ConcretizerOp;
import hu.bme.mit.theta.analysis.algorithm.cegar.ItpRefutation;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;

public class StsExprSeqConcretizer implements ConcretizerOp<ExprState, StsAction, ItpRefutation> {

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
	public CexStatus concretize(final Trace<? extends ExprState, StsAction> cex) {
		checkNotNull(cex);
		checkArgument(cex.length() > 0);
		concreteCex = Optional.empty();
		refutation = Optional.empty();

		final List<ItpMarker> markers = new ArrayList<>(cex.length() + 1);
		for (int i = 0; i < cex.length() + 1; ++i) {
			markers.add(solver.createMarker());
		}

		final ItpPattern pattern = solver.createSeqPattern(markers);

		solver.push();
		solver.add(markers.get(0), sts.unfoldInit(0));
		for (int i = 0; i < cex.length(); ++i) {
			solver.add(markers.get(i), sts.unfoldInv(i));
			solver.add(markers.get(i), sts.unfold(cex.getState(i).toExpr(), i));
			if (i > 0) {
				solver.add(markers.get(i), sts.unfoldTrans(i - 1));
			}
		}
		solver.add(markers.get(cex.length()), sts.unfold(negProp, cex.length() - 1));

		final boolean concretizable = solver.check().isSat();

		if (concretizable) {
			final List<Valuation> trace = sts.extractTrace(solver.getModel(), cex.length());
			final List<ExplState> explStateTrace = trace.stream().map(s -> ExplState.create(s))
					.collect(Collectors.toList());
			concreteCex = Optional.of(new Trace<>(explStateTrace, cex.getActions()));
		} else {
			final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
			for (int i = 0; i < markers.size() - 1; ++i) {
				interpolants.add(sts.foldin(solver.getInterpolant(pattern).eval(markers.get(i)), i));
			}
			refutation = Optional.of(ItpRefutation.createSequence(interpolants));
		}

		solver.pop();

		return getStatus();
	}

	@Override
	public CexStatus getStatus() {
		if (concreteCex.isPresent()) {
			assert (!refutation.isPresent());
			return CexStatus.CONCRETE;
		} else if (refutation.isPresent()) {
			assert (!concreteCex.isPresent());
			return CexStatus.SPURIOUS;
		} else {
			throw new IllegalStateException("No counterexample or refutation is present!");
		}
	}

	@Override
	public ItpRefutation getRefutation() {
		checkState(getStatus() == CexStatus.SPURIOUS);
		assert (refutation.isPresent());
		return refutation.get();
	}

}
