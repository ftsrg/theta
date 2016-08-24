package hu.bme.mit.inf.ttmc.code;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;
import hu.bme.mit.inf.ttmc.frontend.cfa.FunctionToCFATransformer;
import hu.bme.mit.inf.ttmc.frontend.dependency.ControlDependencyGraph;
import hu.bme.mit.inf.ttmc.frontend.dependency.DominatorTree;
import hu.bme.mit.inf.ttmc.frontend.dependency.UseDefineChain;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.GlobalContext;
import hu.bme.mit.inf.ttmc.frontend.ir.utils.IrPrinter;
import hu.bme.mit.inf.ttmc.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.ttmc.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.ttmc.frontend.transform.FunctionSlicer;

class Application {

	public static void main(String[] args)
			throws CoreException, FileNotFoundException, IOException, InterruptedException {

		GlobalContext context = Compiler.compile("all.c");

		context.functions().forEach(s -> {
			System.out.println("===============" + s.getName() + "===============");
			System.out.println("------" + "CFG" + "------");
			System.out.println(IrPrinter.toGraphvizString(s));
			System.out.println("------" + "CFA" + "------");
			CFA cfa = FunctionToCFATransformer.createSBE(s);

			System.out.println(CFAPrinter.toGraphvizSting(cfa));


//			System.out.println("------" + "Dominators" + "------");
//			DominatorTree dt = DominatorTree.createDominatorTree(s);
//			System.out.println(IrPrinter.dominatorTreeGraph(dt));
//

//			System.out.println("------" + "Constant prop" + "------");
//			ConstantPropagator constProp = new ConstantPropagator();
//			constProp.transform(s);
//			System.out.println(IrPrinter.toGraphvizString(s));
//
//			System.out.println("------" + "Dead branch elim" + "------");
//			DeadBranchEliminator dbe = new DeadBranchEliminator();
//			dbe.transform(s);
//			System.out.println(IrPrinter.toGraphvizString(s));
//
//			s.normalize();
//			System.out.println("------" + "final CFG" + "------");
//			System.out.println(IrPrinter.toGraphvizString(s));
//
//			System.out.println("------" + "PDT" + "------");
//			DominatorTree pdt = DominatorTree.createPostDominatorTree(s);
//			System.out.println(IrPrinter.dominatorTreeGraph(pdt));
//
//			System.out.println("------" + "slicer" + "------");
//			FunctionSlicer slicer = new FunctionSlicer();
//			List<Function> slices = slicer.allSlices(s, FunctionSlicer.SLICE_ON_ASSERTS);
//
//			slices.forEach(f -> {
//				System.out.println("---" + "slice" + "---");
//				System.out.println(IrPrinter.toGraphvizString(f));
//				System.out.println("---" + "cfa" + "---");
//			});

		});
	}
}
