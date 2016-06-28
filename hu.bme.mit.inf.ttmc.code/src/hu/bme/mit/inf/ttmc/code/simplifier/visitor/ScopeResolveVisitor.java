package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import java.util.Stack;

import hu.bme.mit.inf.ttmc.code.TransformException;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.util.SymbolTable;

public class ScopeResolveVisitor extends SimplifyAstVisitor {

	private int uniqid = 0;
	
	SymbolTable<String> symbols = new SymbolTable<String>();
	
	@Override
	public StatementAst visit(CompoundStatementAst ast) {
		symbols.pushScope();
		StatementAst res = super.visit(ast);
		symbols.popScope();
		
		return res;
	}

	@Override
	public DeclaratorAst visit(InitDeclaratorAst ast) {
		String name = ast.getName();
		
		if (symbols.currentScopeContains(name))
			throw new TransformException(String.format("Redeclaration of identifier %s.", name));
		
		if (symbols.contains(name)) {
			String newName = String.format("%s_conf%d", name, uniqid++);
			symbols.put(name, newName);
			return new InitDeclaratorAst(newName, ast.getInitializer());
		} else {
			symbols.put(name, name);
		}
		
		return ast;
	}
	
	@Override
	public ExpressionAst visit(NameExpressionAst ast) {
		String name = ast.getName();
		
		if (!symbols.contains(name)) {
			throw new TransformException(String.format("Use of undeclared identifier %s.", name));
		}
		
		String mappedName = symbols.get(name);
		
		if (name == mappedName)
			return ast;
		
		return new NameExpressionAst(mappedName);
	}
	
	
}
