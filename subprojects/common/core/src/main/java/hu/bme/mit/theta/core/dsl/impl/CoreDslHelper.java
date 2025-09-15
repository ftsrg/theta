/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.DeclContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.DeclListContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ExprContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.ExprListContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.StmtContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.StmtListContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.TypeContext;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

public final class CoreDslHelper {

    private CoreDslHelper() {}

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
            return declListCtx.decls.stream().map(CoreDslHelper::createParamDecl).collect(toList());
        }
    }

    public static Type createType(final TypeContext typeCtx) {
        final Type type = typeCtx.accept(TypeCreatorVisitor.getInstance());
        assert type != null;
        return type;
    }

    public static Expr<?> createExpr(final Scope scope, final ExprContext exprCtx) {
        final Expr<?> expr = exprCtx.accept(new ExprCreatorVisitor(scope));
        assert expr != null;
        return expr;
    }

    public static List<Expr<?>> createExprList(
            final Scope scope, final ExprListContext exprListCtx) {
        if (exprListCtx == null || exprListCtx.exprs == null) {
            return Collections.emptyList();
        } else {
            final List<Expr<?>> exprs =
                    exprListCtx.exprs.stream().map(ctx -> createExpr(scope, ctx)).collect(toList());
            return exprs;
        }
    }

    public static Expr<BoolType> createBoolExpr(final Scope scope, final ExprContext exprCtx) {
        return TypeUtils.cast(createExpr(scope, exprCtx), Bool());
    }

    public static List<Expr<BoolType>> createBoolExprList(
            final Scope scope, final ExprListContext exprListCtx) {
        final List<Expr<?>> exprs = createExprList(scope, exprListCtx);
        final List<Expr<BoolType>> boolExprs =
                exprs.stream().map(e -> TypeUtils.cast(e, Bool())).collect(toList());
        return boolExprs;
    }

    public static Stmt createStmt(final Scope scope, final StmtContext stmtCtx) {
        final Stmt stmt = stmtCtx.accept(new StmtCreatorVisitor(scope));
        assert stmt != null;
        return stmt;
    }

    public static List<Stmt> createStmtList(final Scope scope, final StmtListContext stmtListCtx) {
        if (stmtListCtx == null || stmtListCtx.stmts.isEmpty()) {
            return Collections.emptyList();
        } else {
            final List<Stmt> stmts =
                    stmtListCtx.stmts.stream().map(ctx -> createStmt(scope, ctx)).collect(toList());
            return stmts;
        }
    }

    public static DeclSymbol resolveDecl(final Scope scope, final String name) {
        final Optional<? extends Symbol> optSymbol = scope.resolve(name);

        checkArgument(optSymbol.isPresent());
        final Symbol symbol = optSymbol.get();

        checkArgument(symbol instanceof DeclSymbol);
        final DeclSymbol declSymbol = (DeclSymbol) symbol;

        return declSymbol;
    }
}
