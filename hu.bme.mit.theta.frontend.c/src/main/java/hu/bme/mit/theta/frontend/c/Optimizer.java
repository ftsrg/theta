package hu.bme.mit.theta.frontend.c;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.utils.IrPrinter;
import hu.bme.mit.theta.frontend.c.transform.Transformer;
import hu.bme.mit.theta.frontend.c.transform.slicer.FunctionSlicer;

public class Optimizer {

	private final List<Transformer> transforms = new ArrayList<>();
	private final FunctionSlicer slicer;
	
	private final GlobalContext context;
	
	private Predicate<IrNode> slicerPred = FunctionSlicer.SLICE_ON_ASSERTS;

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

	public List<Function> createSlices() {
		List<Function> result = new ArrayList<>();
		
		for (Function func : this.context.functions()) {
			// Don't bother with disabled functions
			if (!func.isEnabled())
				continue;

			List<BasicBlock> blocks = func.getBlocksDFS();
			
			for (BasicBlock block : blocks) {
				for (IrNode node : block.getAllNodes()) {
					if (this.slicerPred.test(node)) {
						Function slice = this.slicer.slice(func, node);
						result.add(slice);
					}
				}
			}
		}
		
		return result;
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
