package hu.bme.mit.inf.ttmc.code.simplifier;

import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.CombinedAssignUnrollVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.visitor.UnrollDeclarationsVisitor;

public class AstSimplifier {

	  private static SimplifyAstVisitor[] visitors = new SimplifyAstVisitor[] {
//		new ForToWhileStatementVisitor(),
//		new SwitchToIfElseVisitor(),
		new UnrollDeclarationsVisitor(),
//		new BreakContinueToGotoVisitor(),
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
