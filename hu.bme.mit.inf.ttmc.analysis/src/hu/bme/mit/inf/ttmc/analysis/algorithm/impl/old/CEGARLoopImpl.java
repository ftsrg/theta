package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.old;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.old.CEGARLoop;
import hu.bme.mit.inf.ttmc.analysis.algorithm.old.Checker;
import hu.bme.mit.inf.ttmc.analysis.algorithm.old.Concretizer;
import hu.bme.mit.inf.ttmc.analysis.algorithm.old.Refiner;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.refutation.Refutation;
import hu.bme.mit.inf.ttmc.formalism.Formalism;

public class CEGARLoopImpl<F extends Formalism, S extends State, P extends Precision, R extends Refutation> implements CEGARLoop<P> {

	private final Checker<F, S, ? super P> checker;
	private final Concretizer<F, ? super S, R> concretizer;
	private final Refiner<S, P, R> refiner;

	private Optional<Counterexample<ExplState>> concreteCex;

	private CEGARLoopImpl(final Checker<F, S, ? super P> checker, final Concretizer<F, ? super S, R> concretizer, final Refiner<S, P, R> refiner) {
		this.checker = checker;
		this.concretizer = concretizer;
		this.refiner = refiner;
		this.concreteCex = Optional.empty();
	}

	public static <F extends Formalism, S extends State, P extends Precision, R extends Refutation> CEGARLoop<P> create(final Checker<F, S, ? super P> checker,
			final Concretizer<F, ? super S, R> concretizer, final Refiner<S, P, R> refiner) {
		return new CEGARLoopImpl<>(checker, concretizer, refiner);
	}

	@Override
	public boolean check(final P initPrecision) {
		P precision = initPrecision;
		Optional<Counterexample<S>> abstractResult;
		this.concreteCex = Optional.empty();
		Counterexample<ExplState> concrCex = null;

		do {
			abstractResult = checker.check(precision);

			if (abstractResult.isPresent()) {
				System.out.println("Abstract Cex: " + abstractResult.get()); // TODO: use logging instead
				if (concretizer.check(abstractResult.get())) {
					concrCex = concretizer.getConcreteCex();
					System.out.println("Concrete Cex: " + concrCex); // TODO: use logging instead
				} else {
					precision = refiner.refine(precision, abstractResult.get(), concretizer.getRefutation());
					System.out.println("New precision: " + precision); // TODO: use logging instead
				}
			}
		} while (abstractResult.isPresent() && concrCex == null);

		return concrCex == null;
	}

	@Override
	public Counterexample<ExplState> getConcreteCex() {
		if (!concreteCex.isPresent())
			throw new IllegalStateException("Concrete counterexample is not present!");
		return concreteCex.get();
	}

}
