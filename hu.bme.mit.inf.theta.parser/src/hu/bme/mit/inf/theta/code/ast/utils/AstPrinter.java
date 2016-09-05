package hu.bme.mit.inf.theta.code.ast.utils;

import hu.bme.mit.inf.theta.code.ast.AstNode;

public class AstPrinter {

	private static int nodeId = 0;
	
	public static String toGraphvizString(AstNode node) {
		StringBuilder sb = new StringBuilder();
	    sb.append("digraph G {");
        printTree(node, sb);
        sb.append("}");
        
        return sb.toString();
	}
	
	private AstPrinter() {}
	
	private static String printTree(AstNode node, StringBuilder sb) {		
		String nodeName = "node_" + nodeId++;
	    sb.append(String.format("%s [label=\"%s\"];\n", nodeName, node.getClass().getSimpleName()));
	    for (AstNode child : node.getChildren()) {
	        String cname = printTree(child, sb);
	        sb.append(String.format("%s -> %s;\n", nodeName, cname));
	    }
	    
	    return nodeName;
	}
	
}
