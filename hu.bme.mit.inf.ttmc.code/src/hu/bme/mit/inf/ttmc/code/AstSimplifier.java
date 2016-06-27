package hu.bme.mit.inf.ttmc.code;

import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.visitor.BreakContinueToGotoVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.ExpressionListUnrollStatementVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.ForToWhileStatementVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.StatementAstTransformerVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.SwitchToIfElseVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.UnaryExpressionUnrollStatementVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.UnrollDeclarationsVisitor;

public class AstSimplifier {

	public static FunctionDefinitionAst simplify(FunctionDefinitionAst ast) {
		CompoundStatementAst prev = ast.getBody();
		
		StatementAstTransformerVisitor[] statementVisitors = new StatementAstTransformerVisitor[] {
			new ForToWhileStatementVisitor(),
			new SwitchToIfElseVisitor(),
			new UnrollDeclarationsVisitor(),
			new UnaryExpressionUnrollStatementVisitor(),
			new BreakContinueToGotoVisitor(),
			new ExpressionListUnrollStatementVisitor(),
		};
		
		CompoundStatementAst body = prev;
		
		for (StatementAstTransformerVisitor visitor : statementVisitors) {
		}
		
		
		return new FunctionDefinitionAst(ast.getName(), ast.getDeclarationSpecifier(), ast.getDeclarator(), body);
	}
	
}
