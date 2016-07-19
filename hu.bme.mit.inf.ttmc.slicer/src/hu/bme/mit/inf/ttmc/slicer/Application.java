package hu.bme.mit.inf.ttmc.slicer;

import hu.bme.mit.inf.ttmc.code.Compiler;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphPrinter;
import hu.bme.mit.inf.ttmc.slicer.optimizer.LoopUnroller;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGBuilder;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGPrinter;
import hu.bme.mit.inf.ttmc.slicer.dependence.LoopAnalysis;
import hu.bme.mit.inf.ttmc.slicer.dependence.PDG;
import hu.bme.mit.inf.ttmc.slicer.dependence.PDGPrinter;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTree;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeCreator;

public class Application {

	public static void main(String[] args) {

		ProcDecl<? extends Type> body = Compiler.createStmts("all.c").get(0);

		CFG cfg = CFGBuilder.createCFG(body);
		System.out.println(CFGPrinter.toGraphvizString(cfg));

		DominatorTree dom = DominatorTreeCreator.dominatorTree(cfg);
		//System.out.println(GraphPrinter.toGraphvizString(dom));

		LoopAnalysis loopAnal = new LoopAnalysis(cfg);
		LoopUnroller loopUnroll = new LoopUnroller(1);
		CFG trans = loopUnroll.transform(cfg);

		System.out.println(CFGPrinter.toGraphvizString(trans));
	}

}
