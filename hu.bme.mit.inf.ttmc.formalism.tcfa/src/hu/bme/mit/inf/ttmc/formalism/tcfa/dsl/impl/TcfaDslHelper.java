package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Param;
import static hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils.cast;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static java.util.stream.Collectors.toList;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.common.dsl.Symbol;
import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.dsl.DeclSymbol;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.ConstDeclContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.DeclContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.DeclListContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.ExprContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.ExprListContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.StmtContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.StmtListContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.TypeContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.VarDeclContext;

final class TcfaDslHelper {

	private TcfaDslHelper() {
	}

	public static ParamDecl<?> createParamDecl(final DeclContext declCtx) {
		final String name = declCtx.name.getText();
		final Type type = createType(declCtx.ttype);
		final ParamDecl<?> paramDecl = Param(name, type);
		return paramDecl;
	}

	public static List<ParamDecl<?>> createParamList(final DeclListContext declListCtx) {
		if (declListCtx == null || declListCtx.decls == null) {
			return Collections.emptyList();
		} else {
			return declListCtx.decls.stream().map(TcfaDslHelper::createParamDecl).collect(toList());
		}
	}

	public static ConstDecl<?> createConstDecl(final DeclContext declCtx) {
		final String name = declCtx.name.getText();
		final Type type = createType(declCtx.ttype);
		final ConstDecl<?> constDecl = Const(name, type);
		return constDecl;
	}

	public static VarDecl<?> createVarDecl(final DeclContext declCtx) {
		final String name = declCtx.name.getText();
		final VarDecl<?> varDecl;

		if (declCtx.ttype.clockType() == null) {
			final Type type = createType(declCtx.ttype);
			varDecl = Var(name, type);
		} else {
			varDecl = Clock(name);
		}

		return varDecl;
	}

	public static Type createType(final TypeContext typeCtx) {
		final Type type = typeCtx.accept(TcfaTypeCreatorVisitor.getInstance());
		assert type != null;
		return type;
	}

	public static Expr<?> createExpr(final Scope scope, final ExprContext exprCtx) {
		final Expr<?> expr = exprCtx.accept(new TcfaExprCreatorVisitor(scope));
		assert expr != null;
		return expr;
	}

	public static List<Expr<?>> createExprList(final Scope scope, final ExprListContext exprListCtx) {
		if (exprListCtx == null || exprListCtx.exprs == null) {
			return Collections.emptyList();
		} else {
			final List<Expr<?>> exprs = exprListCtx.exprs.stream().map(ctx -> createExpr(scope, ctx)).collect(toList());
			return exprs;
		}
	}

	public static Expr<? extends BoolType> createBoolExpr(final Scope scope, final ExprContext exprCtx) {
		return cast(createExpr(scope, exprCtx), BoolType.class);
	}

	public static List<Expr<? extends BoolType>> createBoolExprList(final Scope scope,
			final ExprListContext exprListCtx) {
		final List<Expr<?>> exprs = createExprList(scope, exprListCtx);
		final List<Expr<? extends BoolType>> boolExprs = exprs.stream()
				.map(e -> (Expr<? extends BoolType>) cast(e, BoolType.class)).collect(toList());
		return boolExprs;
	}

	public static Stmt createStmt(final Scope scope, final StmtContext stmtCtx) {
		final Stmt stmt = stmtCtx.accept(new TcfaStmtCreatorVisitor(scope));
		assert stmt != null;
		return stmt;
	}

	public static List<Stmt> createStmtList(final Scope scope, final StmtListContext stmtListCtx) {
		if (stmtListCtx == null || stmtListCtx.stmts.isEmpty()) {
			return Collections.emptyList();
		} else {
			final List<Stmt> stmts = stmtListCtx.stmts.stream().map(ctx -> createStmt(scope, ctx)).collect(toList());
			return stmts;
		}
	}

	public static Decl<?, ?> resolveDecl(final Scope scope, final String name) {
		final Optional<Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof DeclSymbol);
		final DeclSymbol declSymbol = (DeclSymbol) symbol;
		final Decl<?, ?> decl = declSymbol.getDecl();

		return decl;
	}

	public static void declareConstDecls(final Scope scope, final List<? extends ConstDeclContext> constDeclCtxs) {
		for (final ConstDeclContext constDeclCtx : constDeclCtxs) {
			declareConstDecl(scope, constDeclCtx);
		}
	}

	private static void declareConstDecl(final Scope scope, final ConstDeclContext constDeclCtx) {
		final ConstDecl<?> constDecl = createConstDecl(constDeclCtx.ddecl);
		final Symbol symbol = new DeclSymbol(constDecl);
		scope.declare(symbol);
	}

	public static void declareVarDecls(final Scope scope, final List<? extends VarDeclContext> varDeclCtxs) {
		for (final VarDeclContext varDeclCtx : varDeclCtxs) {
			declareVarDecl(scope, varDeclCtx);
		}
	}

	private static void declareVarDecl(final Scope scope, final VarDeclContext varDeclCtx) {
		final VarDecl<?> varDecl = createVarDecl(varDeclCtx.ddecl);
		final Symbol symbol = new DeclSymbol(varDecl);
		scope.declare(symbol);
	}

}
