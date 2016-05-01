package hu.bme.mit.inf.ttmc.code.ast.visitor;

import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;

public interface StatementVisitor<S> {

	public S visit(IfStatementAst ast);
	public S visit(CompoundStatementAst ast);
	public S visit(DeclarationStatementAst ast);
	public S visit(ReturnStatementAst ast);
	public S visit(ExpressionStatementAst ast);
	public S visit(WhileStatementAst ast);
	public S visit(ForStatementAst ast);
	public S visit(DoStatementAst ast);
	public S visit(SwitchStatementAst ast);
	public S visit(CaseStatementAst ast);
	public S visit(DefaultStatementAst ast);
	public S visit(ContinueStatementAst ast);
	public S visit(BreakStatementAst ast);
	public S visit(GotoStatementAst ast);
	public S visit(LabeledStatementAst ast);
	public S visit(NullStatementAst ast);
	
}
