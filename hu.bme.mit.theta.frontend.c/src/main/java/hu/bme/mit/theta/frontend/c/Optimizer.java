package hu.bme.mit.theta.frontend.c;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.frontend.c.cfa.FunctionToCFATransformer;
import hu.bme.mit.theta.frontend.c.cfa.SbeToLbeTransformer;
import hu.bme.mit.theta.frontend.c.dependency.ProgramDependency;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.utils.IrPrinter;
import hu.bme.mit.theta.frontend.c.transform.Transformer;
import hu.bme.mit.theta.frontend.c.transform.slicer.FunctionSlicer;

public class Optimizer {

	private final List<Transformer> transforms = new ArrayList<>();
	private final FunctionSlicer slicer;
	
	private final GlobalContext context;

	private Logger log = NullLogger.getInstance();

	public Optimizer(GlobalContext context, FunctionSlicer slicer) {
		this.context = context;
		this.slicer = slicer;
	}
	
	public void addTransformation(Transformer pass) {
		this.transforms.add(pass);
	}

	public void transform() {
		// Perform global transformations
		for (Transformer pass : this.transforms) {
			this.log.writeln(String.format("Executing transformation pass '%s'", pass.getTransformationName()), 7);
			pass.transform(this.context);
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
			this.log.writeln(IrPrinter.programDependencyGraph(ProgramDependency.buildPDG(fun)), 7);
		});
	}

	public Logger getLogger() {
		return log;
	}

	public void setLogger(Logger log) {
		this.log = log;
	}

}
