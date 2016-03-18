package hu.bme.mit.inf.ttmc.cegar.common;

import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractResult;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IChecker;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IConcretizer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IInitializer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IRefiner;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.NullLogger;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * A class representing a general CEGAR loop. It needs four steps that work on
 * the same type of abstraction: initial abstraction, model checking,
 * counterexample concretization, abstraction refinement.
 *
 * @author Akos
 * @param <AbstractSystemType>
 *            Type of the abstract system
 * @param <AbstractStateType>
 *            Type of the abstract states
 */
public class GenericCEGARLoop<AbstractSystemType extends IAbstractSystem, AbstractStateType extends IAbstractState> implements ICEGARLoop {
	private final IInitializer<AbstractSystemType> initializer; // Initial abstraction creator
	private final IChecker<AbstractSystemType, AbstractStateType> checker; // Model checker
	private final IConcretizer<AbstractSystemType, AbstractStateType> concretizer; // Counterexample concretizer
	private final IRefiner<AbstractSystemType, AbstractStateType> refiner; // Abstraction refiner
	//private IDebugger<AbstractSystemType, AbstractStateType> debugger;         // Debugger (can be null)
	private final ILogger logger; // Logger
	private final String name; // Name of the algorithm
	private final Stopwatch stopwatch; // Stopwatch for measuring runtime

	private volatile boolean isStopped;

	@Override
	public void stop() {
		isStopped = true;
	}

	/**
	 * Constructor, initialize the CEGAR loop with steps
	 *
	 * @param initializer
	 *            Initial abstraction creator
	 * @param checker
	 *            Model checker
	 * @param concretizer
	 *            Counterexample concretizer
	 * @param refiner
	 *            Abstraction refiner
	 * @param debugger
	 *            Debugger, or null to disable debugging
	 * @param logger
	 *            Logger
	 */
	public GenericCEGARLoop(final IInitializer<AbstractSystemType> initializer, final IChecker<AbstractSystemType, AbstractStateType> checker,
			final IConcretizer<AbstractSystemType, AbstractStateType> concretizer, final IRefiner<AbstractSystemType, AbstractStateType> refiner,
			//IDebugger<AbstractSystemType, AbstractStateType> debugger,
			final ILogger logger, final String name) {
		this.initializer = initializer;
		this.checker = checker;
		this.concretizer = concretizer;
		this.refiner = refiner;
		//this.debugger = debugger;
		this.logger = logger == null ? new NullLogger() : logger;
		this.name = name == null ? "" : name;
		this.stopwatch = Stopwatch.createUnstarted();

		isStopped = false;
	}

	@Override
	public CEGARResult check(final STS concreteSystem) {
		isStopped = false;
		// Reset stopwatch
		stopwatch.reset();
		long start = 0;
		stopwatch.start();
		int refinementCount = 0; // Number of refinement iterations
		long initializerTime = 0, checkerTime = 0, concretizerTime = 0, refinerTime = 0;
		int totalStates = 0;

		// Create initial abstraction
		logger.writeTitle("Creating initial abstraction (" + refinementCount + ")", 1);
		start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
		AbstractSystemType abstractSystem = initializer.create(concreteSystem);
		initializerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;

		AbstractResult<AbstractStateType> abstractResult = null; // Abstract result: counterexample or inductive invariant
		ConcreteTrace concreteTrace = null; // Concrete trace corresponding to the abstract cex

		// Main CEGAR loop: model check -> concretize -> refine
		do {
			if (isStopped)
				return null;
			//if (debugger != null) debugger.explore(system).visualize();

			// Do the model checking
			logger.writeTitle("Model checking (" + refinementCount + ")", 1);
			start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
			abstractResult = checker.check(abstractSystem);
			checkerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;
			totalStates += abstractResult.getStateSpaceSize();
			concreteTrace = null; // Reset the concrete trace

			if (isStopped)
				return null;

			// If an abstract counterexample was found, try to concretize it
			if (abstractResult.isCounterExample()) {
				//if (debugger != null) debugger.setAbstractCE(abstractResult.getCounterexample()).visualize();

				// Try to concretize abstract counterexample
				logger.writeTitle("Concretizing counterexample (" + refinementCount + ")", 1);
				start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
				concreteTrace = concretizer.concretize(abstractSystem, abstractResult.getCounterexample());
				concretizerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;

				if (isStopped)
					return null;

				//if (debugger != null) debugger.setConcreteTrace(concreteTrace).visualize();

				// If no concrete counterexample is found the abstract one is spurious
				// and the abstraction has to be refined
				if (!concreteTrace.isCounterexample()) {
					// Refine the abstraction
					logger.writeTitle("Abstraction refinement (" + refinementCount + ")", 1);
					start = stopwatch.elapsed(TimeUnit.MILLISECONDS);
					abstractSystem = refiner.refine(abstractSystem, abstractResult.getCounterexample(), concreteTrace);
					refinerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - start;
					++refinementCount;
					if (isStopped)
						return null;
				}
			}
			if (isStopped)
				return null;
			// Loop until the specification holds or a concrete counterexample is found
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
			result = new CEGARResult(abstractSystem.getSystem(), concreteTrace, stopwatch.elapsed(TimeUnit.MILLISECONDS), refinementCount, detailedTime,
					totalStates, abstractSystem);
		else
			result = new CEGARResult(abstractSystem.getSystem(), abstractResult.getExploredStates(), stopwatch.elapsed(TimeUnit.MILLISECONDS), refinementCount,
					detailedTime, totalStates, abstractSystem);
		printResult(result);
		return result;
	}

	/**
	 * Print the result.
	 *
	 * @param result
	 *            Result of the algorithm
	 */
	private void printResult(final CEGARResult result) {
		logger.writeTitle("Done", 0);
		logger.writeln("Elapsed time: " + result.getElapsedMillis() + " ms", 0);
		for (final Entry<String, Long> entry : result.getDetailedTime().entrySet())
			logger.writeln(String.format(Locale.ENGLISH, "%4.1f", entry.getValue() / (float) result.getElapsedMillis() * 100) + "% " + entry.getKey(), 1, 1);
		logger.writeln("Refinement iterations: " + result.getRefinementCount(), 0);
		logger.writeln("Result: " + (result.specificationHolds() ? "specification holds" : "counterexample found"), 0);
		if (result.getCounterExample() != null) {
			for (final AndExpr m : result.getCounterExample())
				logger.writeln(m, 1, 1);
		}
	}

	@Override
	public String toString() {
		return "CEGAR[" + name + /* (debugger != null ? ", debugmode" : "") + */ "]" + " Init[" + initializer + "]" + " Check[" + checker + "]" + " Concr["
				+ concretizer + "]" + " Refin[" + refiner + "]";
	}
}
