package hu.bme.mit.inf.theta.core.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import hu.bme.mit.inf.theta.common.dsl.BasicScope;
import hu.bme.mit.inf.theta.common.dsl.Scope;
import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.dsl.gen.CoreDslLexer;
import hu.bme.mit.inf.theta.core.dsl.gen.CoreDslParser;
import hu.bme.mit.inf.theta.core.dsl.impl.ExprCreatorVisitor;
import hu.bme.mit.inf.theta.core.dsl.impl.TypeCreatorVisitor;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;

public final class CoreDslManager {

	private final Scope scope;

	public CoreDslManager() {
		this.scope = new BasicScope(null);
	}

	public void declare(final Decl<?, ?> decl) {
		checkNotNull(decl);
		scope.declare(new DeclSymbol(decl));
	}

	public Type parseType(final String string) {
		checkNotNull(string);
		final CoreDslParser parser = createParserForString(string);
		final ParseTree tree = parser.type();
		return tree.accept(TypeCreatorVisitor.getInstance());
	}

	public Expr<?> parseExpr(final String string) {
		checkNotNull(string);
		final CoreDslParser parser = createParserForString(string);
		final ParseTree tree = parser.expr();
		return tree.accept(new ExprCreatorVisitor(scope));
	}

	private static CoreDslParser createParserForString(final String string) {
		final ANTLRInputStream input = new ANTLRInputStream(string);
		final CoreDslLexer lexer = new CoreDslLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final CoreDslParser parser = new CoreDslParser(tokens);
		return parser;
	}

}
