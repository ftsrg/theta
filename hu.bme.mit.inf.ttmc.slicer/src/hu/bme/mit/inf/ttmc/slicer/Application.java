package hu.bme.mit.inf.ttmc.slicer;


import hu.bme.mit.inf.ttmc.code.Compiler;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFACreator;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphPrinter;
import hu.bme.mit.inf.ttmc.slicer.pdg.DominanceTree;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDG;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDGPrinter;
import hu.bme.mit.inf.ttmc.slicer.pdg.PostDominanceTree;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGBuilder;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGPrinter;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dominators.DominatorTreeCreator;

public class Application {

	public static void main(String[] args) {

		ProcDecl<? extends Type> body = Compiler.createStmts("simple.c").get(0);

		CFG cfg = CFGBuilder.createCFG(body);

		CFA cfa = CFACreator.createSBE(body.getStmt().get());

		//System.out.println(CFGPrinter.toGraphvizString(cfg));
		//System.out.println(CFAPrinter.toGraphvizSting(cfa));

		System.out.println(GraphPrinter.toGraphvizString(cfg));


		PostDominanceTree fdt =	PostDominanceTree.fromCFG(cfg);
		System.out.println(GraphPrinter.toGraphvizString(fdt));

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
					System.out.println(GraphPrinter.toGraphvizString(slice));
				}
			}
		}*/
		System.out.println(CFGPrinter.toGraphvizString(cfg));


		DominatorTreeCreator.dominatorTree(cfg);


		//PDG pdg = PDGTransformer.createPDG(cfg);
		//System.out.println(GraphPrinter.toGraphvizString(pdg));
	}

}
