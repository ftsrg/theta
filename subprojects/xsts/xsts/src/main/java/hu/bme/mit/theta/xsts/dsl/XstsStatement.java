package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.*;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
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
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XstsStatement {

	private final DynamicScope scope;
	private final SymbolTable typeTable;
	private final StmtContext context;

	public XstsStatement(final DynamicScope scope, final SymbolTable typeTable, final StmtContext context) {
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

		private DynamicScope currentScope;
		private final SymbolTable typeTable;
		private final Env env;

		public StmtCreatorVisitor(final DynamicScope scope, final SymbolTable typeTable, final Env env) {
			this.currentScope = checkNotNull(scope);
			this.typeTable = checkNotNull(typeTable);
			this.env = checkNotNull(env);
		}

		private void push() {
			currentScope = new BasicDynamicScope(currentScope);
			env.push();
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
			final Expr<BoolType> expr = cast(expression.instantiate(env), Bool());
			return Assume(expr);
		}

		@Override
		public Stmt visitAssignStmt(final AssignStmtContext ctx) {
			try{
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
			catch (Exception e){
				throw new ParseException(ctx,e.getMessage());
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
		public Stmt visitLoopStmt(LoopStmtContext ctx) {
			push();

			final String loopVarId = ctx.loopVar.getText();
			if(currentScope.resolve(loopVarId).isPresent()) throw new ParseException(ctx,String.format("Loop variable %s is already declared in this scope.",loopVarId));
			final var decl = Decls.Var(loopVarId,Int());
			final Symbol symbol = DeclSymbol.of(decl);
			currentScope.declare(symbol);
			env.define(symbol, decl);

			final Expr<IntType> from = cast(new XstsExpression(currentScope, typeTable, ctx.from).instantiate(env),Int());
			final Expr<IntType> to = cast(new XstsExpression(currentScope, typeTable, ctx.to).instantiate(env),Int());
			final Stmt stmt = ctx.subStmt.accept(this);

			pop();

			return LoopStmt.of(stmt,decl,from,to);
		}

		@Override
		public Stmt visitLocalVarDeclStmt(LocalVarDeclStmtContext ctx) {
			final String name = ctx.name.getText();
			final Type type = new XstsType(typeTable,ctx.ttype).instantiate(env);
			final var decl = Decls.Var(name,type);
			final Symbol symbol = DeclSymbol.of(decl);


			final Stmt result;
			if(ctx.initValue==null){
				result = SkipStmt.getInstance();
			} else {
				var expr = new XstsExpression(currentScope,typeTable,ctx.initValue).instantiate(env);
				if (expr.getType().equals(decl.getType())) {
					@SuppressWarnings("unchecked") final VarDecl<Type> tVar = (VarDecl<Type>) decl;
					@SuppressWarnings("unchecked") final Expr<Type> tExpr = (Expr<Type>) expr;
					result = Assign(tVar, tExpr);
				} else {
					throw new IllegalArgumentException("Type of " + decl + " is incompatilbe with " + expr);
				}
			}

			currentScope.declare(symbol);
			env.define(symbol, decl);

			return result;
		}

		@Override
		public Stmt visitBlockStmt(BlockStmtContext ctx) {
			push();
			if(ctx.stmts.size()==0) return SkipStmt.getInstance();
			if(ctx.stmts.size()==1) return ctx.stmt.accept(this);

			final List<Stmt> stmts = new ArrayList<>();
			for(var stmtCtx: ctx.stmts){
				final Stmt stmt = stmtCtx.accept(this);
				stmts.add(stmt);
			}
			pop();
			return SequenceStmt.of(stmts);
		}

	}

}
