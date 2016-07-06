package hu.bme.mit.inf.ttmc.slicer;

import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Skip;

import java.util.ArrayList;

import hu.bme.mit.inf.ttmc.code.Compiler;
import hu.bme.mit.inf.ttmc.common.Tuple;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFACreator;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphPrinter;
import hu.bme.mit.inf.ttmc.slicer.pdg.DominanceTree;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDG;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDGPrinter;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDGTransformer;
import hu.bme.mit.inf.ttmc.slicer.pdg.PostDominanceTree;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGBuilder;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGPrinter;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.*;
import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.*;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.*;

public class Application {

	public static void main(String[] args) {

		ProcDecl<? extends Type> body = Compiler.createStmts("simple.c").get(0);

		CFG cfg = CFGBuilder.createCFG(body);
		CFA cfa = CFACreator.createSBE(body.getStmt().get());

		//System.out.println(CFGPrinter.toGraphvizString(cfg));
		//System.out.println(CFAPrinter.toGraphvizSting(cfa));

		System.out.println(GraphPrinter.toGraphvizString(cfg));

		DominanceTree dt =	DominanceTree.fromCFG(cfg);
		System.out.println(GraphPrinter.toGraphvizString(dt));

		PostDominanceTree fdt =	PostDominanceTree.fromCFG(cfg);
		System.out.println(GraphPrinter.toGraphvizString(fdt));

		PDG pdg = PDG.fromCFG(cfg);

		System.out.println(PDGPrinter.toGraphvizString(pdg));

		//PDG pdg = PDGTransformer.createPDG(cfg);
		//System.out.println(GraphPrinter.toGraphvizString(pdg));
	}

}
