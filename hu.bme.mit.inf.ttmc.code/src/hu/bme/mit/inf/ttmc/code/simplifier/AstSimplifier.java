package hu.bme.mit.inf.ttmc.code.simplifier;

import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.AssignmentUnrollVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.BreakContinueToGotoVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.CombinedAssignUnrollVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.ExpressionListUnrollVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.ForToWhileStatementVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.ScopeResolveVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.SwitchToIfElseVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.UnaryExpressionUnrollVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.UnrollDeclarationsVisitor;

public class AstSimplifier {

	  private static SimplifyAstVisitor[] visitors = new SimplifyAstVisitor[] {
//		new ForToWhileStatementVisitor(),
//		new SwitchToIfElseVisitor(),
		new UnrollDeclarationsVisitor(),
//		new BreakContinueToGotoVisitor(),
//		new UnaryExpressionUnrollVisitor(),
		new CombinedAssignUnrollVisitor(),
//		new ExpressionListUnrollVisitor(),
//		new AssignmentUnrollVisitor(),
//		new ScopeResolveVisitor()
	};

	public static TranslationUnitAst simplify(TranslationUnitAst ast) {
		TranslationUnitAst prev = ast;

		for (SimplifyAstVisitor visitor : visitors) {
			ast = prev.accept(visitor);
			prev = ast;
		}

		return ast;
	}

}
