package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.ItpRefutation;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Concretizer;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.impl.CounterexampleImpl;
import hu.bme.mit.inf.ttmc.analysis.impl.ItpRefutationImpl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;

public class STSExprSeqConcretizer implements Concretizer<STS, ExprState, ItpRefutation> {

	private final STS sts;
	private final ItpSolver solver;
	private final Expr<? extends BoolType> negProp;

	private Optional<Counterexample<ExplState>> concreteCex;
	private Optional<ItpRefutation> refutation;

	private STSExprSeqConcretizer(final STS sts, final ItpSolver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
		this.negProp = Exprs.Not(checkNotNull(sts.getProp()));
		this.concreteCex = Optional.empty();
		this.refutation = Optional.empty();
	}

	@Override
	public boolean check(final Counterexample<? extends ExprState> abstractCex) {
		checkNotNull(abstractCex);
		checkArgument(abstractCex.size() > 0);
		concreteCex = Optional.empty();
		refutation = Optional.empty();

		final List<ItpMarker> markers = new ArrayList<>(abstractCex.size() + 1);
		for (int i = 0; i < abstractCex.size() + 1; ++i) {
			markers.add(solver.createMarker());
		}

		final ItpPattern pattern = solver.createSeqPattern(markers);

		solver.push();
		solver.add(markers.get(0), sts.unrollInit(0));
		for (int i = 0; i < abstractCex.size(); ++i) {
			solver.add(markers.get(i), sts.unrollInv(i));
			solver.add(markers.get(i), sts.unroll(abstractCex.get(i).toExpr(), i));
			if (i > 0) {
				solver.add(markers.get(i), sts.unrollTrans(i - 1));
			}
		}
		solver.add(markers.get(abstractCex.size()), sts.unroll(negProp, abstractCex.size() - 1));

		final boolean concretizable = solver.check().boolValue();

		if (concretizable) {
			final List<Valuation> trace = sts.extractTrace(solver.getModel(), abstractCex.size());
			concreteCex = Optional.of(CounterexampleImpl.create(trace.stream().map(s -> ExplState.create(s)).collect(Collectors.toList())));
		} else {
			final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
			for (int i = 0; i < markers.size() - 1; ++i) {
				interpolants.add(sts.foldin(solver.getInterpolant(pattern).eval(markers.get(i)), i));
				refutation = Optional.of(ItpRefutationImpl.createSequence(interpolants));
			}
		}

		solver.pop();

		return concretizable;
	}

	@Override
	public Counterexample<ExplState> getConcreteCex() {
		if (!concreteCex.isPresent())
			throw new IllegalStateException("No counterexample is present!");
		return concreteCex.get();
	}

	@Override
	public ItpRefutation getRefutation() {
		if (!refutation.isPresent())
			throw new IllegalStateException("No refutation is present!");
		return refutation.get();
	}

}
