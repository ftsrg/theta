package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Concretizer;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.impl.CounterexampleImpl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSExprConcretizer implements Concretizer<STS, ExprState> {

	private final Solver solver;
	private final STS sts;
	private final Expr<? extends BoolType> negProp;
	private boolean genPrefix;

	private Optional<Counterexample<ExplState>> concreteCex;
	private Optional<Counterexample<ExplState>> prefix;

	public static STSExprConcretizer create(final STS sts, final Solver solver, final boolean genPrefix) {
		return new STSExprConcretizer(sts, solver, genPrefix);
	}

	private STSExprConcretizer(final STS sts, final Solver solver, final boolean genPrefix) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
		this.negProp = Exprs.Not(checkNotNull(sts.getProp()));
		this.genPrefix = genPrefix;
		this.concreteCex = Optional.empty();
		this.prefix = Optional.empty();
	}

	@Override
	public void setGenPrefix(final boolean genPrefix) {
		this.genPrefix = genPrefix;
	}

	@Override
	public boolean getGenPrefix() {
		return genPrefix;
	}

	@Override
	public boolean check(final Counterexample<? extends ExprState> abstractCex) {
		checkNotNull(abstractCex);
		checkArgument(abstractCex.size() > 0);
		concreteCex = Optional.empty();
		prefix = Optional.empty();

		if (genPrefix) {
			return checkWithPrefix(abstractCex);
		} else {
			return checkWithoutPrefix(abstractCex);
		}
	}

	private boolean checkWithPrefix(final Counterexample<? extends ExprState> abstractCex) {
		Model model = null;
		int prefixLen = 0;
		solver.push();
		solver.add(sts.unrollInit(0));
		for (int i = 0; i < abstractCex.size(); ++i) {
			solver.add(sts.unrollInv(i));
			solver.add(sts.unroll(abstractCex.get(i).toExpr(), i));
			if (i > 0) {
				solver.add(sts.unrollTrans(i - 1));
			}
			solver.check();
			if (solver.getStatus().boolValue()) {
				model = solver.getModel();
				prefixLen = i + 1;
			} else {
				break;
			}
		}

		assert model != null; // For i==0 it must be satisfiable (abstract initial states should contain at least one concrete initial state)

		if (prefixLen == abstractCex.size()) {
			solver.add(sts.unroll(negProp, abstractCex.size() - 1));
			solver.check();
			if (solver.getStatus().boolValue()) {
				model = solver.getModel();
			}
		}

		final List<Valuation> trace = sts.extractTrace(model, prefixLen);
		prefix = Optional.of(CounterexampleImpl.create(trace.stream().map(s -> ExplState.create(s)).collect(Collectors.toList())));
		if (solver.getStatus().boolValue()) {
			concreteCex = prefix;
		}

		final boolean concretizable = solver.check().boolValue();

		solver.pop();

		return concretizable;
	}

	private boolean checkWithoutPrefix(final Counterexample<? extends ExprState> abstractCex) {
		solver.push();
		solver.add(sts.unrollInit(0));
		for (int i = 0; i < abstractCex.size(); ++i) {
			solver.add(sts.unrollInv(i));
			solver.add(sts.unroll(abstractCex.get(i).toExpr(), i));
			if (i > 0) {
				solver.add(sts.unrollTrans(i - 1));
			}
		}
		solver.add(sts.unroll(negProp, abstractCex.size() - 1));

		final boolean concretizable = solver.check().boolValue();

		if (concretizable) {
			final List<Valuation> trace = sts.extractTrace(solver.getModel(), abstractCex.size());
			concreteCex = Optional.of(CounterexampleImpl.create(trace.stream().map(s -> ExplState.create(s)).collect(Collectors.toList())));
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
	public Counterexample<ExplState> getPrefix() {
		if (!getGenPrefix())
			throw new IllegalStateException("Prefix generation is turned off!");
		if (!prefix.isPresent())
			throw new IllegalStateException("No prefix is present!");
		return prefix.get();
	}

}
