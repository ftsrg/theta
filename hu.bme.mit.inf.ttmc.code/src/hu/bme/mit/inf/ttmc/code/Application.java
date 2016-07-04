package hu.bme.mit.inf.ttmc.code;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.utils.AstPrinter;
import hu.bme.mit.inf.ttmc.code.visitor.PrintCodeAstVisitor;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;

class Application {
	
	public static void main(String[] args)
			throws CoreException, FileNotFoundException, IOException, InterruptedException {
	
		TranslationUnitAst root = Compiler.createAst("simple.c");
		
		graphvizOutput("ast_custom", AstPrinter.toGraphvizString(root));
		
		//CFA cfa = Compiler.createSBE("simple.c");
		
		TranslationUnitAst newRoot = Compiler.createSimplifiedAst("simple.c");
		graphvizOutput("ast_trans", AstPrinter.toGraphvizString(newRoot));
		
		PrintCodeAstVisitor printer = new PrintCodeAstVisitor();
		System.out.println(newRoot.accept(printer));
		
		//System.out.println(CFAPrinter.toGraphvizSting(cfa))

		System.out.println(Compiler.createStmts("simple.c").get(0).getStmt().get());
		
		List<CFA> cfas = Compiler.createSBE("simple.c");
		
		for (CFA cfa : cfas) {
			System.out.println(CFAPrinter.toGraphvizSting(cfa));
		}
	}

	private static int nodeId = 0;

	private static String getCdtAstString(IASTNode ast)
	{
		StringBuilder sb = new StringBuilder();
		sb.append("digraph G {");
		printTree(ast, sb);
		sb.append("}");
		
		return sb.toString();
	}
	
	private static String printTree(IASTNode node, StringBuilder sb) {
		String nodeName = "node_" + nodeId++;
		sb.append(String.format("%s [label=\"%s\"];\n", nodeName, node.getClass().getSimpleName()));
		for (IASTNode child : node.getChildren()) {
			String cname = printTree(child, sb);
			sb.append(String.format("%s -> %s;\n", nodeName, cname));
		}

		return nodeName;
	}

	private static void graphvizOutput(String basename, String content) {
		try {
			FileOutputStream fos = new FileOutputStream(new File(basename + ".dot"));
			OutputStreamWriter osw = new OutputStreamWriter(fos);

			osw.write(content);
			osw.close();

			Process proc = Runtime.getRuntime().exec(String.format("dot -Tpng -o %s.png %s.dot", basename, basename));
			proc.waitFor();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
