package hu.bme.mit.inf.ttmc.code;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.CharBuffer;
import java.util.ArrayList;

import javax.xml.transform.Transformer;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.gnu.c.GCCLanguage;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.parser.FileContent;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.ScannerInfo;
import org.eclipse.cdt.core.parser.util.StringUtil;
import org.eclipse.cdt.internal.core.index.CIndex;
import org.eclipse.cdt.internal.core.index.IIndexFragment;
import org.eclipse.cdt.internal.core.parser.ParserLogService;
import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.utils.AstPrinter;
import hu.bme.mit.inf.ttmc.code.ast.visitor.CloneAstVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.AstSimplifier;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.stmt.visitor.PrintStmtVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.PrintCodeAstVisitor;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFACreator;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.WhileStmt;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.formalism.program.impl.ProgramManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;

class Application {

	// scope, deklarációs lista, postfix/prefix

	
	public static void main(String[] args)
			throws CoreException, FileNotFoundException, IOException, InterruptedException {
	
		Compiler compiler = new Compiler();
		CFA cfa = compiler.createLBE("hello.c");
		
		System.out.println(CFAPrinter.toGraphvizSting(cfa));
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

	private static IASTTranslationUnit parseFile(String file) throws CoreException {
		GCCLanguage lang = new GCCLanguage();

		FileContent fc = FileContent.createForExternalFileLocation(file);
		ScannerInfo sc = new ScannerInfo();
	
		IncludeFileContentProvider ifcp = IncludeFileContentProvider.getEmptyFilesProvider();
		CIndex index = new CIndex(null);
	
		IParserLogService log = new ParserLogService(null);
	
		IASTTranslationUnit ast = lang.getASTTranslationUnit(fc, sc, ifcp, index, 0, log);
		
		return ast;		
	}

}
