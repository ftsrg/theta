package hu.bme.mit.inf.ttmc.cegar.common;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractResult;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Checker;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Initializer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Refiner;
import hu.bme.mit.inf.ttmc.cegar.common.utils.debugging.Debugger;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * A class representing a general CEGAR loop. It needs four steps that work on
 * the same type of abstraction: initial abstraction, model checking,
 * counterexample concretization, abstraction refinement.
 */
public class GenericCEGARLoop<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState> implements CEGARLoop {
	private final Initializer<AbstractSystemType> initializer;
	private final Checker<AbstractSystemType, AbstractStateType> checker;
	private final Concretizer<AbstractSystemType, AbstractStateType> concretizer;
	private final Refiner<AbstractSystemType, AbstractStateType> refiner;
	private final Debugger<AbstractSystemType, AbstractStateType> debugger; // Can be null
	private final Logger logger;
	private final String name;
	private final Stopwatch stopwatch;

	private volatile boolean isStopped;

	@Override
	public void stop() {
		isStopped = true;
		initializer.stop();
		checker.stop();
		concretizer.stop();
		refiner.stop();
	}

	@Override
	public void resetStop() {
		isStopped = false;
		initializer.resetStop();
		checker.resetStop();
		concretizer.resetStop();
		refiner.resetStop();
	}

	public GenericCEGARLoop(final Initializer<AbstractSystemType> initializer, final Checker<AbstractSystemType, AbstractStateType> checker,
			final Concretizer<AbstractSystemType, AbstractStateType> concretizer, final Refiner<AbstractSystemType, AbstractStateType> refiner,
			final Debugger<AbstractSystemType, AbstractStateType> debugger, final Logger logger, final String name) {
		this.initializer = checkNotNull(initializer);
		this.checker = checkNotNull(checker);
		this.concretizer = checkNotNull(concretizer);
		this.refiner = checkNotNull(refiner);
		this.debugger = debugger; // Can be null
		this.logger = logger == null ? new NullLogger() : logger;
		this.name = name == null ? "" : name;
		this.stopwatch = Stopwatch.createUnstarted();

		isStopped = false;
	}

	@Override
	public CEGARResult check(final STS concreteSys) {
		checkNotNull(concreteSys);
		resetStop();

		stopwatch.reset();
		long start = 0;
		stopwatch.start();
		int refinementIterations = 0;
		long initializerTime = 0, checkerTime = 0, concretizerTime = 0, refinerTime = 0;
		int totalStates = 0;

		// Create initial abstraction
		logger.writeHeader("Creating initial abstraction (" + refinementIterations + ")", 1);
		start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
		AbstractSystemType abstractSystem = initializer.create(concreteSys);
		if (isStopped)
			return null;
		initializerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;

		AbstractResult<AbstractStateType> abstractResult = null;
		ConcreteTrace concreteTrace = null;

		// Main CEGAR loop: model check -> concretize -> refine
		do {
			if (isStopped)
				return null;
			if (debugger != null)
				debugger.clearStateSpace().explore(abstractSystem).visualize();

			// Do the model checking
			logger.writeHeader("Model checking (" + refinementIterations + ")", 1);
			start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
			abstractResult = checker.check(abstractSystem);
			if (isStopped)
				return null;
			checkerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;
			totalStates += abstractResult.getStateSpaceSize();
			concreteTrace = null;

			if (abstractResult.isCounterExample()) {
				if (debugger != null)
					debugger.setAbstractCE(abstractResult.getCounterexample()).visualize();

				// Try to concretize abstract counterexample
				logger.writeHeader("Concretizing counterexample (" + refinementIterations + ")", 1);
				start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
				concreteTrace = concretizer.concretize(abstractSystem, abstractResult.getCounterexample());
				if (isStopped)
					return null;
				concretizerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;

				if (debugger != null)
					debugger.setConcreteTrace(concreteTrace).visualize();

				// If no concrete counterexample is found the abstract one is spurious and the abstraction has to be refined
				if (!concreteTrace.isCounterexample()) {
					// Refine the abstraction
					logger.writeHeader("Abstraction refinement (" + refinementIterations + ")", 1);
					start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
					abstractSystem = refiner.refine(abstractSystem, abstractResult.getCounterexample(), concreteTrace);
					if (isStopped)
						return null;
					refinerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;
					++refinementIterations;
				}
			}
			if (isStopped)
				return null;
		} while (abstractResult.isCounterExample() && !concreteTrace.isCounterexample());

		stopwatch.stop();

		final Map<String, Long> detailedTime = new HashMap<>();
		detailedTime.put("Initializer", initializerTime);
		detailedTime.put("Checker", checkerTime);
		detailedTime.put("Concretizer", concretizerTime);
		detailedTime.put("Refiner", refinerTime);

		// Create result, print and return
		CEGARResult result = null;
		if (abstractResult.isCounterExample())
			result = new CEGARResult(abstractSystem.getSTS(), concreteTrace, stopwatch.elapsed(TimeUnit.MILLISECONDS), refinementIterations, detailedTime,
					totalStates, abstractSystem);
		else
			result = new CEGARResult(abstractSystem.getSTS(), abstractResult.getExploredStates(), stopwatch.elapsed(TimeUnit.MILLISECONDS),
					refinementIterations, detailedTime, totalStates, abstractSystem);
		printResult(result);
		return result;
	}

	private void printResult(final CEGARResult result) {
		logger.writeHeader("Done", 0);
		logger.writeln("Elapsed time: " + result.getElapsedMillis() + " ms", 0);
		for (final Entry<String, Long> entry : result.getDetailedTime().entrySet())
			logger.writeln(String.format(Locale.ENGLISH, "%4.1f", entry.getValue() / (float) result.getElapsedMillis() * 100) + "% " + entry.getKey(), 1, 1);
		logger.writeln("Refinement iterations: " + result.getRefinementCount(), 0);
		logger.writeln("Result: " + (result.propertyHolds() ? "specification holds" : "counterexample found"), 0);
		if (result.getCounterExample() != null) {
			for (final AndExpr m : result.getCounterExample())
				logger.writeln(m, 1, 1);
		}
	}

	@Override
	public String toString() {
		return "CEGAR[" + name + (debugger != null ? ", debugmode" : "") + "]" + " Init[" + initializer + "]" + " Check[" + checker + "]" + " Concr["
				+ concretizer + "]" + " Refin[" + refiner + "]";
	}
}
