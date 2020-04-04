/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
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
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.ConstDeclContext;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.DeclContext;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.DeclListContext;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.ExprContext;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.ExprListContext;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.TypeContext;
import hu.bme.mit.theta.xsts.dsl.gen.StsDslParser.VarDeclContext;

final class StsDslHelper {

	private StsDslHelper() {
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
			return declListCtx.decls.stream().map(StsDslHelper::createParamDecl).collect(toList());
		}
	}

	public static ConstDecl<?> createConstDecl(final ConstDeclContext constDeclCtx) {
		final DeclContext declCtx = constDeclCtx.ddecl;
		final String name = declCtx.name.getText();
		final Type type = createType(declCtx.ttype);
		final ConstDecl<?> constDecl = Const(name, type);
		return constDecl;
	}

	public static VarDecl<?> createVarDecl(final VarDeclContext varDeclCtx) {
		final DeclContext declCtx = varDeclCtx.ddecl;
		final String name = declCtx.name.getText();
		final Type type = createType(declCtx.ttype);
		final VarDecl<?> varDecl = Var(name, type);
		return varDecl;
	}

	public static Substitution createConstDefs(final Scope scope, final Substitution assignment,
											   final List<? extends ConstDeclContext> constDeclCtxs) {
		final Map<Decl<?>, Expr<?>> declToExpr = new HashMap<>();
		for (final ConstDeclContext constDeclCtx : constDeclCtxs) {
			addDef(scope, assignment, declToExpr, constDeclCtx);
		}
		return BasicSubstitution.builder().putAll(declToExpr).build();
	}

	private static void addDef(final Scope scope, final Substitution assignment, final Map<Decl<?>, Expr<?>> declToExpr,
							   final ConstDeclContext constDeclCtx) {
		final String name = constDeclCtx.ddecl.name.getText();
		final DeclSymbol declSymbol = resolveDecl(scope, name);
		final Decl<?> decl = declSymbol.getDecl();
		final Expr<?> expr = createExpr(scope, assignment, constDeclCtx.value);
		declToExpr.put(decl, expr);
	}

	public static Type createType(final TypeContext typeCtx) {
		final Type type = typeCtx.accept(StsTypeCreatorVisitor.getInstance());
		assert type != null;
		return type;
	}

	public static Expr<?> createExpr(final Scope scope, final Substitution assignment, final ExprContext exprCtx) {
		final Expr<?> expr = exprCtx.accept(new StsExprCreatorVisitor(scope, assignment));
		assert expr != null;
		return expr;
	}

	public static List<Expr<?>> createExprList(final Scope scope, final Substitution assignment,
											   final ExprListContext exprListCtx) {
		if (exprListCtx == null || exprListCtx.exprs == null) {
			return Collections.emptyList();
		} else {
			final List<Expr<?>> exprs = exprListCtx.exprs.stream().map(ctx -> createExpr(scope, assignment, ctx))
					.collect(toList());
			return exprs;
		}
	}

	public static Expr<BoolType> createBoolExpr(final Scope scope, final Substitution assignment,
												final ExprContext exprCtx) {
		return TypeUtils.cast(createExpr(scope, assignment, exprCtx), Bool());
	}

	public static List<Expr<BoolType>> createBoolExprList(final Scope scope, final Substitution assignment,
														  final ExprListContext exprListCtx) {
		final List<Expr<?>> exprs = createExprList(scope, assignment, exprListCtx);
		final List<Expr<BoolType>> boolExprs = exprs.stream().map(e -> TypeUtils.cast(e, Bool())).collect(toList());
		return boolExprs;
	}

	public static DeclSymbol resolveDecl(final Scope scope, final String name) {
		final Optional<? extends Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof DeclSymbol);
		final DeclSymbol declSymbol = (DeclSymbol) symbol;

		return declSymbol;
	}

	public static StsDeclSymbol resolveSts(final Scope scope, final String name) {
		final Optional<? extends Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof StsDeclSymbol);
		final StsDeclSymbol stsSymbol = (StsDeclSymbol) symbol;

		return stsSymbol;
	}

}
