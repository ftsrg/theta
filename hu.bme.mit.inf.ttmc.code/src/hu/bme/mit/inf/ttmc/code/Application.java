package hu.bme.mit.inf.ttmc.code;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.CharBuffer;
import java.util.ArrayList;

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
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.stmt.visitor.PrintStmtVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.PrintCodeAstVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.StatementUnrollAstVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.TransformProgramVisitor;
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
	
	public static void main(String[] args) throws CoreException, FileNotFoundException, IOException, InterruptedException {
	    
	    GCCLanguage lang = new GCCLanguage();
	    
	    FileContent fc = FileContent.createForExternalFileLocation("hello.c");
	    ScannerInfo sc = new ScannerInfo();
	    
	    IncludeFileContentProvider ifcp = IncludeFileContentProvider.getEmptyFilesProvider();
	    CIndex index = new CIndex(null);
	    
	    IParserLogService log = new ParserLogService(null);
	    
	    IASTTranslationUnit ast = lang.getASTTranslationUnit(fc, sc, ifcp, index, 0, log);
	    
	    //ast.accept(visitor);
	    	    
	    StringBuilder sb = new StringBuilder();
	    sb.append("digraph G {");
        printTree(ast, sb);
        sb.append("}");

        try {
            FileOutputStream fos = new FileOutputStream(new File("ast_cdt.dot"));
            OutputStreamWriter osw = new OutputStreamWriter(fos);
            
            osw.write(sb.toString());
            osw.close();
            
            Process proc = Runtime.getRuntime().exec("dot -Tpng -o ast_cdt.png ast_cdt.dot");
			proc.waitFor();
		} catch (Exception e) {
			e.printStackTrace();
		}
        
	    TranslationUnitAst root = AstTransformer.transform(ast);

	    sb.setLength(0);
	    sb.append("digraph G {");
        printCustomTree(root, sb);
        sb.append("}");
	            
        try {
            FileOutputStream fos = new FileOutputStream(new File("ast_custom.dot"));
            OutputStreamWriter osw = new OutputStreamWriter(fos);
            
            osw.write(sb.toString());
            osw.close();
            
            Process proc = Runtime.getRuntime().exec("dot -Tpng -o ast_custom.png ast_custom.dot");
			proc.waitFor();
		} catch (Exception e) {
			e.printStackTrace();
		}	    
	    
	    SimplifyAstVisitor simplVisitor = new SimplifyAstVisitor();
	    StatementUnrollAstVisitor unroll = new StatementUnrollAstVisitor();

	    FunctionDefinitionAst main = (FunctionDefinitionAst) root.getChildren()[0];
	    FunctionDefinitionAst mainSimpl = (FunctionDefinitionAst) (main.accept(unroll).accept(simplVisitor));
	    
	    PrintCodeAstVisitor codePrinter = new PrintCodeAstVisitor();
	    
	    String code = mainSimpl.accept(codePrinter);
	    
	    System.out.println(code);
	    
	    
	    sb.setLength(0);
	    sb.append("digraph G {");
        printCustomTree(mainSimpl, sb);
        sb.append("}");
	            
        try {
            FileOutputStream fos = new FileOutputStream(new File("ast_trans.dot"));
            OutputStreamWriter osw = new OutputStreamWriter(fos);
            
            osw.write(sb.toString());
            osw.close();
            
            Process proc = Runtime.getRuntime().exec("dot -Tpng -o ast_trans.png ast_trans.dot");
			proc.waitFor();
		} catch (Exception e) {
			e.printStackTrace();
		}	

	    ProgramManager manager = new ProgramManagerImpl(new ConstraintManagerImpl());
	    TransformProgramVisitor visitor = new TransformProgramVisitor(manager);
	    
	    Stmt content = mainSimpl.getBody().accept(visitor);
	    
	    CFA cfa = CFACreator.createSBE(manager, content);
	    CFA cfa2 = CFACreator.createLBE(manager, content);
	    
	    //printStmt(content, 0);
	    
	    System.out.println(content);
	    
	    PrintStmtVisitor stmtVisitor = new PrintStmtVisitor();
	    String s = content.accept(stmtVisitor, new StringBuilder());
	    System.out.println("===============");
	    
	    System.out.println(s);
	    System.out.println("================");

	    System.out.println(CFAPrinter.toGraphvizSting(cfa));
	    System.out.println("================");
	    System.out.println(CFAPrinter.toGraphvizSting(cfa2));
	}
	
	private static int nodeId = 0;
	
	public static String printTree(IASTNode node, StringBuilder sb) {
	    String nodeName = "node_" + nodeId++;
	    sb.append(String.format("%s [label=\"%s\"];\n", nodeName, node.getClass().getSimpleName()));
	    for (IASTNode child : node.getChildren()) {
	        String cname = printTree(child, sb);
	        sb.append(String.format("%s -> %s;\n", nodeName, cname));
	    }
	    
	    return nodeName;
	}
	
	public static String printCustomTree(AstNode node, StringBuilder sb) {
		String nodeName = "node_" + nodeId++;
	    sb.append(String.format("%s [label=\"%s\"];\n", nodeName, node.getClass().getSimpleName()));
	    for (AstNode child : node.getChildren()) {
	        String cname = printCustomTree(child, sb);
	        sb.append(String.format("%s -> %s;\n", nodeName, cname));
	    }
	    
	    return nodeName;
	}
		
	public static void printc(IASTNode node, int depth) {
	    for (IASTNode child : node.getChildren()) {
	        System.out.print(CharBuffer.allocate(depth).toString().replace( '\0', ' ' ));
	        System.out.println(child.getClass());
	        printc(child, depth + 1);
	    }
	}
	

}
