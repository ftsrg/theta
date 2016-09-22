package hu.bme.mit.inf.theta.frontend;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.common.logging.impl.NullLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.frontend.cfa.FunctionToCFATransformer;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.ir.utils.IrPrinter;
import hu.bme.mit.inf.theta.frontend.transform.ContextTransformer;
import hu.bme.mit.inf.theta.frontend.transform.FunctionSlicer;
import hu.bme.mit.inf.theta.frontend.transform.FunctionTransformer;

public class Optimizer {

	private final List<FunctionTransformer> funcTransformers = new ArrayList<>();
	private final List<ContextTransformer> contextTransformers = new ArrayList<>();
	private final FunctionSlicer slicer = new FunctionSlicer();
	private final GlobalContext context;

	private Logger log = new NullLogger();

	public Optimizer(GlobalContext context) {
		this.context = context;
	}

	public void addFunctionTransformer(FunctionTransformer pass) {
		this.funcTransformers.add(pass);
	}

	public void transform() {
		// Perform global transformations
		for (ContextTransformer pass : this.contextTransformers) {
			pass.transform(this.context);
				this.log.writeln(
					String.format("Executing global pass '%s'", pass.getTransformationName()),
					7
				);
		}

		// Perform local function transformations
		for (FunctionTransformer pass : this.funcTransformers) {
			for (Function func : this.context.functions()) {
				this.log.writeln(
					String.format("Executing pass '%s' on function '%s'", pass.getTransformationName(), func.getName()),
					7
				);
				pass.transform(func);
			}
		}
	}

	public List<CFA> createCfaSlices() {
		List<CFA> cfas = new ArrayList<>();

		for (Function func : this.context.functions()) {
			List<Function> slices = this.slicer.allSlices(func, FunctionSlicer.SLICE_ON_ASSERTS);
			cfas.addAll(slices.stream()
				.map(slice -> FunctionToCFATransformer.createSBE(slice))
				.collect(Collectors.toList())
			);
		}

		this.log.writeln(String.format("Found %d slices.", cfas.size()), 7);

		return cfas;
	}

	public List<CFA> createSlices() {
		return this.context.functions().stream().map(func -> FunctionToCFATransformer.createSBE(func)).collect(Collectors.toList());
	}

	public void dump() {
		this.log.writeHeader("DEBUG DUMP of Optimizer.", 7);
		this.context.functions().forEach(fun -> {
			this.log.writeln("-----" + fun.getName() + "-----", 7);
			this.log.writeln(IrPrinter.toGraphvizString(fun), 7);
		});
	}

	public Logger getLogger() {
		return log;
	}

	public void setLogger(Logger log) {
		this.log = log;
	}

}
