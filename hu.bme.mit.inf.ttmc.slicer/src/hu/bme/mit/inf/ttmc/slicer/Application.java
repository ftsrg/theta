package hu.bme.mit.inf.ttmc.slicer;


import hu.bme.mit.inf.ttmc.code.Compiler;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphPrinter;
import hu.bme.mit.inf.ttmc.slicer.optimizer.LocalConstantPropagator;
import hu.bme.mit.inf.ttmc.slicer.cfg.BasicBlockCFGTransformer;
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

		System.out.println(CFGPrinter.toGraphvizString(cfg));
		PDG pdg = PDG.fromCFG(cfg);

		System.out.println(PDGPrinter.toGraphvizString(pdg));

/*
		ReachabilitySlicer slicer = new ReachabilitySlicer();

		for (CFGNode node : cfg.nodes()) {
			if (node instanceof StmtCFGNode) {
				Stmt stmt = ((StmtCFGNode) node).getStmt();
				if (stmt instanceof AssertStmt) {
					CFG slice = slicer.slice(cfg, node);
					System.out.println("Slice on " + stmt);
					System.out.println(CFGPrinter.toGraphvizString(slice));
				}
			}
		}
*/

		CFG bb = BlockCFGTransformer.createBlocks(cfg);
		System.out.println(CFGPrinter.toGraphvizString(bb));

		LocalConstantPropagator constProp = new LocalConstantPropagator();

		constProp.transform(bb);
		System.out.println(CFGPrinter.toGraphvizString(bb));

//		CFG newCfg = BasicBlockCFGTransformer.splitBasicBlocks(bb);
//		System.out.println(GraphPrinter.toGraphvizString(newCfg));
//		PDG newPdg = PDG.fromCFG(newCfg);
//		DominatorTree newPdt = DominatorTreeCreator.postDominatorTree(newCfg);
//
//		System.out.println(PDGPrinter.toGraphvizString(newPdg));
//		System.out.println(GraphPrinter.toGraphvizString(newPdt));
/*
		for (CFGNode node : newCfg.nodes()) {
			if (node instanceof StmtCFGNode) {
				Stmt stmt = ((StmtCFGNode) node).getStmt();
				if (stmt instanceof AssertStmt) {
					CFG slice = slicer.slice(newCfg, node);
					System.out.println("Slice on " + stmt);
					System.out.println(GraphPrinter.toGraphvizString(slice));
				}
			}
		}
*/


		//BasicBlockUseDefineChain ud = new BasicBlockUseDefineChain(bb);
		//CFG bb = BasicBlockCFGTransformer.buildBasicBlocks(cfg);
		//System.out.println(GraphPrinter.toGraphvizString(bb));

		//LocalConstantPropagator constProp = new LocalConstantPropagator();

		//constProp.transform(bb);
		//System.out.println(GraphPrinter.toGraphvizString(bb));


		//PDG pdg = PDGTransformer.createPDG(cfg);
		//System.out.println(GraphPrinter.toGraphvizString(pdg));
	}

}
