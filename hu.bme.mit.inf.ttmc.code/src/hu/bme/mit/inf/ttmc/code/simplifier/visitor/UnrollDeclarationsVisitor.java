package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.StatementListAst;

public class UnrollDeclarationsVisitor extends SimplifyAstVisitor {

	@Override
	public StatementAst visit(DeclarationStatementAst ast) {
		DeclarationAst decl = ast.getDeclaration();
		
		if (decl instanceof VarDeclarationAst) {
			VarDeclarationAst varDecl = (VarDeclarationAst) decl;
			List<DeclaratorAst> declarators = varDecl.getDeclarators();
			
			if (declarators.size() == 1)
				return ast;
			
			List<StatementAst> stmts = new ArrayList<>();
			for (DeclaratorAst declarator : declarators) {				
				stmts.add(new DeclarationStatementAst(new VarDeclarationAst(varDecl.getSpecifier(), ImmutableList.of(declarator))));
			}

			return new StatementListAst(stmts);
		}
		
		return ast;
	}
}
