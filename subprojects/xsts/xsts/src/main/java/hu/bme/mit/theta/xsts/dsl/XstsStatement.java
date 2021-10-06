package hu.bme.mit.theta.xsts.dsl;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.dsl.*;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;
import hu.bme.mit.theta.xsts.type.XstsCustomType;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.*;
import static hu.bme.mit.theta.core.stmt.Stmts.*;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XstsStatement {

    private final DynamicScope scope;
    private final SymbolTable typeTable;
    private final StmtContext context;
    private final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType;

    public XstsStatement(final DynamicScope scope, final SymbolTable typeTable, final StmtContext context, final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType) {
        this.scope = checkNotNull(scope);
        this.typeTable = checkNotNull(typeTable);
        this.context = checkNotNull(context);
        this.varToType = checkNotNull(varToType);
    }

    public Stmt instantiate(final Env env) {
        final StmtCreatorVisitor visitor = new StmtCreatorVisitor(scope, typeTable, env, varToType);
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
        final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType;
        private final Env env;

        public StmtCreatorVisitor(final DynamicScope scope, final SymbolTable typeTable, final Env env, final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType) {
            this.currentScope = checkNotNull(scope);
            this.typeTable = checkNotNull(typeTable);
            this.env = checkNotNull(env);
            this.varToType = checkNotNull(varToType);
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
        @SuppressWarnings("unchecked")
        public Stmt visitHavocStmt(final HavocStmtContext ctx) {
            final String lhsId = ctx.lhs.getText();
            final Symbol lhsSymbol = currentScope.resolve(lhsId).get();
            final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);

            final hu.bme.mit.theta.xsts.type.XstsType type = varToType.get(var);
            if (type instanceof XstsCustomType) {
                final Expr<BoolType> expr = type.createBoundExpr(var);
                final AssumeStmt assume = Assume(expr);
                return SequenceStmt.of(List.of(Havoc(var), assume));
            }

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
            try {
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
            } catch (Exception e) {
                throw new ParseException(ctx, e.getMessage());
            }
        }

        @Override
        public Stmt visitNonDetStmt(NonDetStmtContext ctx) {
            final List<Stmt> stmts = new ArrayList<>();
            for (var block : ctx.blocks) {
                final Stmt stmt = block.accept(this);
                stmts.add(stmt);
            }
            return NonDetStmt.of(stmts);
        }

        @Override
        public Stmt visitAssignArrayWriteSugar(AssignArrayWriteSugarContext ctx) {
            try {
                final String lhsId = ctx.array.getText();
                final Symbol lhsSymbol = currentScope.resolve(lhsId).get();
                final VarDecl<?> var = (VarDecl<?>) env.eval(lhsSymbol);
                checkArgument(var.getType() instanceof ArrayType);

                final XstsExpression index = new XstsExpression(currentScope, typeTable, ctx.index);
                final Expr<?> indexExpr = index.instantiate(env);

                final XstsExpression value = new XstsExpression(currentScope, typeTable, ctx.value);
                final Expr<?> valueExpr = value.instantiate(env);

                final Expr<?> arrayWriteExpr = createArrayWriteExpr(var.getRef(), indexExpr, valueExpr);
                if (arrayWriteExpr.getType().equals(var.getType())) {
                    @SuppressWarnings("unchecked") final VarDecl<Type> tVar = (VarDecl<Type>) var;
                    @SuppressWarnings("unchecked") final Expr<Type> tExpr = (Expr<Type>) arrayWriteExpr;
                    return Assign(tVar, tExpr);
                } else {
                    throw new IllegalArgumentException("Type of " + var + " is incompatilbe with " + arrayWriteExpr);
                }
            } catch (Exception e) {
                throw new ParseException(ctx, e.getMessage());
            }
        }

        private <T1 extends Type, T2 extends Type> Expr<?> createArrayWriteExpr(Expr<?> var, Expr<?> indexExpr, Expr<?> valueExpr) {
            @SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) var;
            final Expr<T1> index = cast(indexExpr, array.getType().getIndexType());
            final Expr<T2> value = cast(valueExpr, array.getType().getElemType());
            return Write(array, index, value);
        }

        @Override
        public Stmt visitLoopStmt(LoopStmtContext ctx) {
            push();

            final String loopVarId = ctx.loopVar.getText();
            if (currentScope.resolve(loopVarId).isPresent())
                throw new ParseException(ctx, String.format("Loop variable %s is already declared in this scope.", loopVarId));
            final var decl = Decls.Var(loopVarId, Int());
            final Symbol symbol = DeclSymbol.of(decl);
            currentScope.declare(symbol);
            env.define(symbol, decl);

            final Expr<IntType> from = cast(new XstsExpression(currentScope, typeTable, ctx.from).instantiate(env), Int());
            final Expr<IntType> to = cast(new XstsExpression(currentScope, typeTable, ctx.to).instantiate(env), Int());
            final Stmt stmt = ctx.subStmt.accept(this);

            pop();

            return LoopStmt.of(stmt, decl, from, to);
        }

        @Override
        @SuppressWarnings("unchecked")
        public Stmt visitLocalVarDeclStmt(LocalVarDeclStmtContext ctx) {
            final String name = ctx.name.getText();
            final hu.bme.mit.theta.xsts.type.XstsType xstsType = new XstsType(typeTable, ctx.ttype).instantiate(env);
            final Type type = xstsType.getType();
            final var decl = Decls.Var(name, type);
            final Symbol symbol = DeclSymbol.of(decl);

            final Stmt result;
            if (ctx.initValue == null) {
                final Stmt havoc = Havoc(decl);
                if (xstsType instanceof XstsCustomType) {
                    final Expr<BoolType> expr = xstsType.createBoundExpr(decl);
                    final AssumeStmt assume = Assume(expr);
                    result = SequenceStmt.of(List.of(havoc, assume));
                } else {
                    result = havoc;
                }
            } else {
                var expr = new XstsExpression(currentScope, typeTable, ctx.initValue).instantiate(env);
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

            final Stmt result;
            if (ctx.stmts.size() == 0) result = SkipStmt.getInstance();
            else if (ctx.stmts.size() == 1) result = ctx.stmt.accept(this);
            else {
                final List<Stmt> stmts = new ArrayList<>();
                for (var stmtCtx : ctx.stmts) {
                    final Stmt stmt = stmtCtx.accept(this);
                    stmts.add(stmt);
                }
                result = SequenceStmt.of(stmts);
            }

            pop();
            return result;
        }

        @Override
        public Stmt visitIfStmt(IfStmtContext ctx) {
            final XstsExpression condExpr = new XstsExpression(currentScope, typeTable, ctx.cond);
            final Expr<BoolType> cond = cast(condExpr.instantiate(env), Bool());

            final Stmt then = ctx.then.accept(this);
            if (ctx.elze == null) {
                return IfStmt.of(cond, then);
            } else {
                final Stmt elze = ctx.elze.accept(this);
                return IfStmt.of(cond, then, elze);
            }
        }
    }

}
