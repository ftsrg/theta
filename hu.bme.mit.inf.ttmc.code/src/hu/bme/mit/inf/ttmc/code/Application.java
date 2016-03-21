package hu.bme.mit.inf.ttmc.code;

import java.nio.CharBuffer;

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
import hu.bme.mit.inf.ttmc.code.ast.AstRoot;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;

class Application {

	public static void main(String[] args) throws CoreException {
	    
	    GCCLanguage lang = new GCCLanguage();
	    
	    FileContent fc = FileContent.createForExternalFileLocation("hello.c");
	    ScannerInfo sc = new ScannerInfo();
	    
	    IncludeFileContentProvider ifcp = IncludeFileContentProvider.getEmptyFilesProvider();
	    CIndex index = new CIndex(null);
	    
	    IParserLogService log = new ParserLogService(null);
	    
	    IASTTranslationUnit ast = lang.getASTTranslationUnit(fc, sc, ifcp, index, 0, log);
	    
	    //ast.accept(visitor);
	    	    
	    System.out.println("digraph G {");
        printTree(ast);
	    System.out.println("}");
	       
	    AstRoot root = AstTransformer.transform(ast);

	    System.out.println("digraph G {");	
	    printCustomTree(root);	    
	    System.out.println("}");
	}
	
	private static int nodeId = 0;
	
	public static String printTree(IASTNode node) {
	    String nodeName = "node_" + nodeId++;
	    System.out.println( String.format("%s [label=\"%s\"];", nodeName, node.getClass().getSimpleName()));
	    for (IASTNode child : node.getChildren()) {
	        String cname = printTree(child);
	        System.out.println(String.format("%s -> %s;", nodeName, cname));
	    }
	    
	    return nodeName;
	}
	
	public static String printCustomTree(AstNode node) {
		String nodeName = "node_" + nodeId++;
	    System.out.println( String.format("%s [label=\"%s\"];", nodeName, node.getClass().getSimpleName()));
	    for (AstNode child : node.getChildren()) {
	        String cname = printCustomTree(child);
	        System.out.println(String.format("%s -> %s;", nodeName, cname));
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
