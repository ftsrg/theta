package hu.bme.mit.inf.ttmc.slicer;


import java.util.List;

import hu.bme.mit.inf.ttmc.code.Compiler;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFACreator;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphPrinter;
import hu.bme.mit.inf.ttmc.slicer.optimizer.DeadBranchEliminator;
import hu.bme.mit.inf.ttmc.slicer.optimizer.GlobalConstantPropagator;
import hu.bme.mit.inf.ttmc.slicer.optimizer.LocalConstantPropagator;
import hu.bme.mit.inf.ttmc.slicer.optimizer.LoopUnroller;
import hu.bme.mit.inf.ttmc.slicer.cfa.CFGToCFATransformer;
import hu.bme.mit.inf.ttmc.slicer.cfg.BlockCFGTransformer;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGBuilder;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGPrinter;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dependence.PDG;
import hu.bme.mit.inf.ttmc.slicer.dependence.PDGPrinter;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTree;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeCreator;

public class Application {

	public static void main(String[] args) {

		ProcDecl<? extends Type> body = Compiler.createStmts("all.c").get(0);

		CFG cfg = CFGBuilder.createCFG(body);

		CFA cfa = CFACreator.createSBE(body.getStmt().get());
		CFA lbe = CFACreator.createLBE(body.getStmt().get());

		System.out.println("============== CFG ==============");
		System.out.println(CFGPrinter.toGraphvizString(cfg));

		System.out.println("============== BasicBlocks ==============");
		CFG bb = BlockCFGTransformer.createBlocks(cfg);
		System.out.println(CFGPrinter.toGraphvizString(bb));

		System.out.println("============== Local const prop ==============");
		LocalConstantPropagator constProp = new LocalConstantPropagator();
		constProp.transform(bb);

		System.out.println(CFGPrinter.toGraphvizString(bb));

		System.out.println("============== Dead branch elim ==============");
		DeadBranchEliminator deadElim = new DeadBranchEliminator();
		deadElim.transform(bb);

		System.out.println(CFGPrinter.toGraphvizString(bb));

		System.out.println("============== Block split ==============");
		CFG split = BlockCFGTransformer.splitBlocks(bb);

		System.out.println(CFGPrinter.toGraphvizString(split));

		System.out.println("============== Global constant prop ==============");
		GlobalConstantPropagator globProp = new GlobalConstantPropagator();

		globProp.transform(split);

		System.out.println(CFGPrinter.toGraphvizString(split));

		System.out.println("============== Blocks again ==============");
		CFG bb2 = BlockCFGTransformer.createBlocks(split);

		System.out.println(CFGPrinter.toGraphvizString(bb2));

		System.out.println("============== Dead branch again ==============");
		deadElim.transform(bb2);

		System.out.println(CFGPrinter.toGraphvizString(bb2));
		System.out.println(CFGPrinter.toGraphvizString(bb2, true));

		System.out.println("============== Block split again ==============");
		CFG split2 = BlockCFGTransformer.splitBlocks(bb2);

		System.out.println(CFGPrinter.toGraphvizString(split2));

		System.out.println("============== Loop unrolling ==============");
		LoopUnroller unroll = new LoopUnroller(10);
		unroll.transform(split2);
		System.out.println(CFGPrinter.toGraphvizString(split2));

		System.out.println("============== Blocks again again ==============");
		CFG bb3 = BlockCFGTransformer.createBlocks(split2);

		System.out.println(CFGPrinter.toGraphvizString(bb3));
		System.out.println("============== Local const prop 2 ==============");
		constProp.transform(bb3);

		System.out.println(CFGPrinter.toGraphvizString(bb3));

		System.out.println("============== Block split again ==============");
		CFG split3 = BlockCFGTransformer.splitBlocks(bb3);

		System.out.println(CFGPrinter.toGraphvizString(split3));

		System.out.println("============== Global constant prop 2 ==============");

		globProp.transform(split3);

		CFG bb4 = BlockCFGTransformer.createBlocks(split3);
		constProp.transform(bb4);

		System.out.println(CFGPrinter.toGraphvizString(split3));
		System.out.println(CFGPrinter.toGraphvizString(bb4));

		for (int i = 0; i < 10; i++) {
			split3 = BlockCFGTransformer.splitBlocks(bb4);
			globProp.transform(split3);
			bb4 = BlockCFGTransformer.createBlocks(split3);
			deadElim.transform(bb4);
			constProp.transform(bb4);
		}

		System.out.println("============== Slices ==============");
		System.out.println(CFGPrinter.toGraphvizString(bb4));
		split3 = BlockCFGTransformer.splitBlocks(bb4);

		ReachabilitySlicer slicer = new ReachabilitySlicer();
		slicer.allSlices(split3, ReachabilitySlicer.SLICE_ON_ASSERTS).forEach(s -> {
			System.out.println(CFGPrinter.toGraphvizString(s));
			CFA cfa2 = CFGToCFATransformer.transform(s);
			System.out.println(CFAPrinter.toGraphvizSting(cfa2));
		});




	}

}