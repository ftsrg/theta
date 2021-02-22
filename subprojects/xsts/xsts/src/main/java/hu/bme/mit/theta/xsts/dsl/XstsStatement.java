package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.*;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class XstsStatement {

	private final Scope scope;
	private final SymbolTable typeTable;
	private final StmtContext context;

	public XstsStatement(final Scope scope, final SymbolTable typeTable, final StmtContext context) {
		this.scope = checkNotNull(scope);
		this.typeTable = checkNotNull(typeTable);
		this.context = checkNotNull(context);
	}

	public Stmt instantiate(final Env env) {
		final StmtCreatorVisitor visitor = new StmtCreatorVisitor(scope, typeTable, env);
		final Stmt stmt = context.accept(visitor);
		if (stmt == null) {
			throw new AssertionError();
		} else {
			return stmt;
		}
	}

	private static final class StmtCreatorVisitor extends XstsDslBaseVisitor<Stmt> {

		private Scope currentScope;
		private final SymbolTable typeTable;
		private final Env env;

		public StmtCreatorVisitor(final Scope scope, final SymbolTable typeTable, final Env env) {
			this.currentScope = checkNotNull(scope);
			this.typeTable = checkNotNull(typeTable);
			this.env = checkNotNull(env);
		}

		private void push(final List<VarDecl<?>> localDecls) {
			final BasicScope scope = new BasicScope(currentScope);
			env.push();
			for (final VarDecl<?> localDecl : localDecls) {
				final Symbol symbol = DeclSymbol.of(localDecl);
				scope.declare(symbol);
				env.define(symbol, localDecl);
			}
			currentScope = scope;
		}

		private void pop() {
			checkState(currentScope.enclosingScope().isPresent(), "Enclosing scope is not present.");
			currentScope = currentScope.enclosingScope().get();
			env.pop();
		}

		@Override
		public Stmt visitHavocStmt(final HavocStmtContext ctx) {
			final String lhsId = ctx.lhs.getText();
			final Symbol lhsSymbol = currentScope.resolve(lhsId).get();
			final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);
			return Havoc(var);
		}

		@Override
		public Stmt visitAssumeStmt(final AssumeStmtContext ctx) {
			final XstsExpression expression = new XstsExpression(currentScope, typeTable, ctx.cond);
			final Expr<BoolType> expr = TypeUtils.cast(expression.instantiate(env), Bool());
			return Assume(expr);
		}

		@Override
		public Stmt visitAssignStmt(final AssignStmtContext ctx) {
			final String lhsId = ctx.lhs.getText();
			final Symbol lhsSymbol = currentScope.resolve(lhsId).get();
			final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);

			final XstsExpression expression = new XstsExpression(currentScope, typeTable, ctx.value);
			final Expr<?> expr = expression.instantiate(env);

			if (expr.getType().equals(var.getType())) {
				@SuppressWarnings("unchecked") final VarDecl<Type> tVar = (VarDecl<Type>) var;
				@SuppressWarnings("unchecked") final Expr<Type> tExpr = (Expr<Type>) expr;
				return Assign(tVar, tExpr);
			} else {
				throw new IllegalArgumentException("Type of " + var + " is incompatilbe with " + expr);
			}
		}

		@Override
		public Stmt visitNonDetStmt(NonDetStmtContext ctx) {
			final List<Stmt> stmts = new ArrayList<>();
			for(var block: ctx.blocks){
				final Stmt stmt = block.accept(this);
				stmts.add(stmt);
			}
			return NonDetStmt.of(stmts);
		}

		@Override
		public Stmt visitSeqStmt(SeqStmtContext ctx) {
			if(ctx.stmts.size()==0) return SkipStmt.getInstance();
			if(ctx.stmts.size()==1) return ctx.stmt.accept(this);

			final List<Stmt> stmts = new ArrayList<>();
			for(var stmtCtx: ctx.stmts){
				final Stmt stmt = stmtCtx.accept(this);
				stmts.add(stmt);
			}
			return SequenceStmt.of(stmts);

		}

		@Override
		public Stmt visitBlockStmt(BlockStmtContext ctx) {
			if(ctx.varDecls.size()>0){
				final List<VarDecl<?>> localDecls = ctx.varDecls.stream()
						.map(d -> createLocalVarDecl(d)).collect(Collectors.toList());

				push(localDecls);

				final Stmt subStmt = ctx.subStmt.accept(this);

				pop();

				return subStmt;
			} else {
				return ctx.subStmt.accept(this);
			}

		}

		private VarDecl<?> createLocalVarDecl(LocalVarDeclContext ctx){
			final String name = ctx.name.getText();
			final Type type = new XstsType(typeTable,ctx.ttype).instantiate(env);
			return Decls.Var(name,type);
		}
	}

}
