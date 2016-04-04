package hu.bme.mit.inf.ttmc.code.ast.visitor;

import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;

public interface StatementVisitor<S> {

	public S visit(IfStatementAst ast);
	public S visit(CompoundStatementAst ast);
	public S visit(VarDeclarationStatementAst ast);
	public S visit(ReturnStatementAst ast);
	public S visit(ExpressionStatementAst ast);
	public S visit(WhileStatementAst ast);
	public S visit(ForStatementAst ast);
	public S visit(DoStatementAst ast);
	
}
