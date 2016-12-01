package hu.bme.mit.theta.frontend.c.parser.ast.visitor;

import hu.bme.mit.theta.frontend.c.parser.ast.BreakStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.CaseStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.CompoundStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.ContinueStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.DeclarationStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.DefaultStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.DoStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.ExpressionStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.ForStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.GotoStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.IfStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.LabeledStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.NullStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.ReturnStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.SwitchStatementAst;
import hu.bme.mit.theta.frontend.c.parser.ast.WhileStatementAst;

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
