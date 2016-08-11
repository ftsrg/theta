package hu.bme.mit.inf.ttmc.core.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.core.dsl.gen.CoreDSLLexer;
import hu.bme.mit.inf.ttmc.core.dsl.gen.CoreDSLParser;
import hu.bme.mit.inf.ttmc.core.dsl.impl.ExprCreatorVisitor;
import hu.bme.mit.inf.ttmc.core.dsl.impl.TypeCreatorVisitor;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public final class CoreDSL {

	private CoreDSL() {
	}

	public static Type parseType(final String string) {
		checkNotNull(string);

		final ANTLRInputStream input = new ANTLRInputStream(string);
		final CoreDSLLexer lexer = new CoreDSLLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final CoreDSLParser parser = new CoreDSLParser(tokens);

		final ParseTree tree = parser.type();
		return tree.accept(TypeCreatorVisitor.getInstance());
	}

	public static Expr<?> parseExpr(final Scope scope, final String string) {
		checkNotNull(string);
		checkNotNull(scope);

		final ANTLRInputStream input = new ANTLRInputStream(string);
		final CoreDSLLexer lexer = new CoreDSLLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final CoreDSLParser parser = new CoreDSLParser(tokens);

		final ParseTree tree = parser.expr();
		return tree.accept(new ExprCreatorVisitor(scope));
	}

}
