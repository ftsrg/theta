package hu.bme.mit.inf.ttmc.code.ast;

import java.util.ArrayList;
import java.util.List;

public class TranslationUnitAst extends AstNode {

	private List<FunctionDefinitionAst> functions;
	
	public TranslationUnitAst(List<FunctionDefinitionAst> functions) {
		this.functions = functions;
	}

	@Override
	public AstNode[] getChildren() {
		return this.functions.toArray(new AstNode[this.functions.size()]);
	}
	
	
	public TranslationUnitAst copy() {
		List<FunctionDefinitionAst> newFunctions = new ArrayList<>();
		
		for (FunctionDefinitionAst func : this.functions) {
			newFunctions.add(func.copy());
		}
		
		return new TranslationUnitAst(newFunctions);
	}
	
}
