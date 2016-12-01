package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.theta.core.decl.impl.Decls.Param;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.cast;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Clock;
import static java.util.stream.Collectors.toList;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ConstDeclContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.DeclContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.DeclListContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ExprContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ExprListContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.StmtContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.StmtListContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.VarDeclContext;

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

	public static Assignment createConstDefs(final Scope scope, final Assignment assignment,
			final List<? extends ConstDeclContext> constDeclCtxs) {
		final Map<Decl<?>, Expr<?>> declToExpr = new HashMap<>();
		for (final ConstDeclContext constDeclCtx : constDeclCtxs) {
			addDef(scope, assignment, declToExpr, constDeclCtx);
		}
		return new AssignmentImpl(declToExpr);
	}

	private static void addDef(final Scope scope, final Assignment assignment, final Map<Decl<?>, Expr<?>> declToExpr,
			final ConstDeclContext constDeclCtx) {
		final String name = constDeclCtx.ddecl.name.getText();
		final DeclSymbol declSymbol = resolveDecl(scope, name);
		final Decl<?> decl = declSymbol.getDecl();
		final Expr<?> expr = createExpr(scope, assignment, constDeclCtx.value);
		declToExpr.put(decl, expr);
	}

	public static Type createType(final TypeContext typeCtx) {
		final Type type = typeCtx.accept(TcfaTypeCreatorVisitor.getInstance());
		assert type != null;
		return type;
	}

	public static Expr<?> createExpr(final Scope scope, final Assignment assignment, final ExprContext exprCtx) {
		final Expr<?> expr = exprCtx.accept(new TcfaExprCreatorVisitor(scope, assignment));
		assert expr != null;
		return expr;
	}

	public static List<Expr<?>> createExprList(final Scope scope, final Assignment assignment,
			final ExprListContext exprListCtx) {
		if (exprListCtx == null || exprListCtx.exprs == null) {
			return Collections.emptyList();
		} else {
			final List<Expr<?>> exprs = exprListCtx.exprs.stream().map(ctx -> createExpr(scope, assignment, ctx))
					.collect(toList());
			return exprs;
		}
	}

	public static Expr<? extends BoolType> createBoolExpr(final Scope scope, final Assignment assignment,
			final ExprContext exprCtx) {
		return cast(createExpr(scope, assignment, exprCtx), BoolType.class);
	}

	public static List<Expr<? extends BoolType>> createBoolExprList(final Scope scope, final Assignment assignment,
			final ExprListContext exprListCtx) {
		final List<Expr<?>> exprs = createExprList(scope, assignment, exprListCtx);
		final List<Expr<? extends BoolType>> boolExprs = exprs.stream()
				.map(e -> (Expr<? extends BoolType>) cast(e, BoolType.class)).collect(toList());
		return boolExprs;
	}

	public static Stmt createStmt(final Scope scope, final Assignment assignment, final StmtContext stmtCtx) {
		final Stmt stmt = stmtCtx.accept(new TcfaStmtCreatorVisitor(scope, assignment));
		assert stmt != null;
		return stmt;
	}

	public static List<Stmt> createStmtList(final Scope scope, final Assignment assignment,
			final StmtListContext stmtListCtx) {
		if (stmtListCtx == null || stmtListCtx.stmts.isEmpty()) {
			return Collections.emptyList();
		} else {
			final List<Stmt> stmts = stmtListCtx.stmts.stream().map(ctx -> createStmt(scope, assignment, ctx))
					.collect(toList());
			return stmts;
		}
	}

	public static DeclSymbol resolveDecl(final Scope scope, final String name) {
		final Optional<Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof DeclSymbol);
		final DeclSymbol declSymbol = (DeclSymbol) symbol;

		return declSymbol;
	}

	public static TcfaSymbol resolveTcfa(final Scope scope, final String name) {
		final Optional<Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof TcfaSymbol);
		final TcfaSymbol tcfaSymbol = (TcfaSymbol) symbol;

		return tcfaSymbol;
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
