package hu.bme.mit.theta.frontend.c;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.frontend.c.cfa.FunctionToCFATransformer;
import hu.bme.mit.theta.frontend.c.cfa.SbeToLbeTransformer;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.utils.IrPrinter;
import hu.bme.mit.theta.frontend.c.transform.ContextTransformer;
import hu.bme.mit.theta.frontend.c.transform.FunctionSlicer;
import hu.bme.mit.theta.frontend.c.transform.FunctionTransformer;

public class Optimizer {

	private final List<FunctionTransformer> funcTransformers = new ArrayList<>();
	private final List<ContextTransformer> contextTransformers = new ArrayList<>();

	private final List<FunctionTransformer> postContextFunctionTransformers = new ArrayList<>();

	private final FunctionSlicer slicer = new FunctionSlicer();
	private final GlobalContext context;

	private Logger log = new NullLogger();

	public Optimizer(GlobalContext context) {
		this.context = context;
	}

	public void addFunctionTransformer(FunctionTransformer pass) {
		this.funcTransformers.add(pass);
	}

	public void addContextTransformer(ContextTransformer pass) {
		this.contextTransformers.add(pass);
	}

	public void addPostContextFunctionTransformer(FunctionTransformer pass) {
		this.postContextFunctionTransformers.add(pass);
	}

	public void transform() {
		// Perform local function transformations
		for (FunctionTransformer pass : this.funcTransformers) {
			List<Function> functions = this.context.functions().stream().filter(f -> f.isEnabled())
					.collect(Collectors.toList());
			for (Function func : functions) {
				this.log.writeln(String.format("Executing pass '%s' on function '%s'", pass.getTransformationName(),
						func.getName()), 7);
				pass.transform(func);
			}
		}

		// Perform global transformations
		for (ContextTransformer pass : this.contextTransformers) {
			pass.transform(this.context);
			this.log.writeln(String.format("Executing global pass '%s'", pass.getTransformationName()), 7);
		}

		// Perform local function transformations
		for (FunctionTransformer pass : this.postContextFunctionTransformers) {
			List<Function> functions = this.context.functions().stream().filter(f -> f.isEnabled())
					.collect(Collectors.toList());
			for (Function func : functions) {
				this.log.writeln(String.format("Executing pass '%s' on function '%s'", pass.getTransformationName(),
						func.getName()), 7);
				pass.transform(func);
			}
		}
	}

	/**
	 * Inlines global variable initialization into 'main'.
	 */
	public void inlineGlobalVariables() {
		Function main = this.context.getFunctionByName("main");
		BasicBlock bb = main.createBlock("globals_init");

		this.context.globals().forEach(glob -> {
			bb.addNode(glob.getAssignment());
		});

		BasicBlock codeEntry = main.getEntryNode().getTarget();
		bb.terminate(NodeFactory.Goto(codeEntry));

		main.getEntryNode().replaceTarget(codeEntry, bb);
		main.normalize();
	}

	public List<CFA> createCfas() {
		return this.context.functions().stream().filter(func -> func.isEnabled())
				.map(func -> FunctionToCFATransformer.createSBE(func)).collect(Collectors.toList());
	}

	public List<CFA> getProgramSlices() {
		Function main = this.context.getFunctionByName("main");
		List<Function> slices = this.slicer.allSlices(main, FunctionSlicer.SLICE_ON_ASSERTS);

		return slices.stream().map(slice -> FunctionToCFATransformer.createSBE(slice)).collect(Collectors.toList());
	}

	public List<CFA> getProgramSlicesLBE() {
		Function main = this.context.getFunctionByName("main");
		List<Function> slices = this.slicer.allSlices(main, FunctionSlicer.SLICE_ON_ASSERTS);

		return slices.stream().map(slice -> FunctionToCFATransformer.createLBE(slice))
				.map(cfa -> SbeToLbeTransformer.transform(cfa)).collect(Collectors.toList());
	}

	public List<Function> createSlices() {
		List<Function> slices = new ArrayList<>();

		this.context.functions().stream().filter(func -> func.isEnabled()).forEach(func -> {
			slices.addAll(this.slicer.allSlices(func, FunctionSlicer.SLICE_ON_ASSERTS));
		});

		this.log.writeln(String.format("Found %d slices.", slices.size()), 7);

		return slices;
	}

	public List<CFA> createCfaSlices(boolean lbe) {
		return this.createSlices().stream().map(slice -> FunctionToCFATransformer.createSBE(slice))
				.map(cfa -> lbe ? SbeToLbeTransformer.transform(cfa) : cfa).collect(Collectors.toList());
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
