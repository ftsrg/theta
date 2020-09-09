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
package hu.bme.mit.theta.xta.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.*;
import hu.bme.mit.theta.xta.utils.ChanType;
import hu.bme.mit.theta.xta.utils.ClockType;
import hu.bme.mit.theta.xta.utils.RangeType;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

final class XtaType {

	private final Scope scope;

	private final TypeContext typeContext;
	private final List<ArrayIndexContext> arrayIndexContexts;

	public XtaType(final Scope scope, final TypeContext typeContext, final List<ArrayIndexContext> arrayIndexContexts) {
		this.scope = checkNotNull(scope);
		this.typeContext = checkNotNull(typeContext);
		this.arrayIndexContexts = checkNotNull(arrayIndexContexts);

		checkArgument(typeContext.fTypePrefix.fUrgent == null);
	}

	public Type instantiate(final Env env) {
		checkNotNull(env);

		final Type basicType = createBasicType(typeContext, env);

		Type result = basicType;

		for (final ArrayIndexContext arrayIndexContext : arrayIndexContexts) {
			final Type indexType = createIndexType(arrayIndexContext, env);
			result = Array(indexType, result);
		}

		return result;
	}

	////

	private Type createBasicType(final TypeContext typeContext, final Env env) {
		final BasicTypeInstantiationVisitor visitor = new BasicTypeInstantiationVisitor(env);
		final BasicTypeContext basicTypeContext = typeContext.fBasicType;
		final Type basicType = basicTypeContext.accept(visitor);
		return basicType;
	}

	private Type createIndexType(final ArrayIndexContext arrayIndexContext, final Env env) {
		final IndexTypeInstantiationVisitor visitor = new IndexTypeInstantiationVisitor(env);
		final Type indexType = arrayIndexContext.accept(visitor);
		return indexType;
	}

	////

	private final class BasicTypeInstantiationVisitor extends XtaDslBaseVisitor<Type> {
		private final Env env;

		private BasicTypeInstantiationVisitor(final Env env) {
			this.env = env;
		}

		@Override
		public Type visitIntType(final IntTypeContext ctx) {
			return Int();
		}

		@Override
		public Type visitBoolType(final BoolTypeContext ctx) {
			return Bool();
		}

		@Override
		public Type visitClockType(final ClockTypeContext ctx) {
			return ClockType.getInstance();
		}

		@Override
		public Type visitChanType(final ChanTypeContext ctx) {
			return ChanType.getInstance();
		}

		@Override
		public Type visitRangeType(final RangeTypeContext ctx) {
			final XtaExpression lowerExpression = new XtaExpression(scope, ctx.fFromExpression);
			final XtaExpression upperExpression = new XtaExpression(scope, ctx.fToExpression);

			final Expr<?> lowerExpr = lowerExpression.instantiate(env);
			final Expr<?> upperExpr = upperExpression.instantiate(env);

			final IntLitExpr lowerLitExpr = (IntLitExpr) ExprUtils.simplify(lowerExpr);
			final IntLitExpr upperLitExpr = (IntLitExpr) ExprUtils.simplify(upperExpr);

			final int lower = lowerLitExpr.getValue().intValue();
			final int upper = upperLitExpr.getValue().intValue();

			final Type result = RangeType.Range(lower, upper);
			return result;
		}

		@Override
		public Type visitRefType(final RefTypeContext ctx) {
			final String id = ctx.fId.getText();
			final Symbol symbol = scope.resolve(id).get();
			final XtaTypeSymbol typeSymbol = (XtaTypeSymbol) symbol;
			final Object value = env.compute(typeSymbol, t -> t.instantiate(env));
			final Type result = (Type) value;
			return result;
		}

	}

	private final class IndexTypeInstantiationVisitor extends XtaDslBaseVisitor<Type> {
		private final Env env;

		public IndexTypeInstantiationVisitor(final Env env) {
			this.env = env;
		}

		@Override
		public Type visitIdIndex(final IdIndexContext ctx) {
			final Symbol symbol = scope.resolve(ctx.fId.getText()).get();
			if (symbol instanceof XtaVariableSymbol) {
				final XtaVariableSymbol variableSymbol = (XtaVariableSymbol) symbol;
				assert variableSymbol.isConstant();
				final Object value = env.compute(variableSymbol, v -> v.instantiate("", env).asConstant().getExpr());

				final IntLitExpr elemCount = (IntLitExpr) value;
				final Type result = RangeType.Range(0, elemCount.getValue().intValue() - 1);
				return result;

			} else if (symbol instanceof XtaTypeSymbol) {
				final XtaTypeSymbol typeSymbol = (XtaTypeSymbol) symbol;
				final Object value = env.compute(typeSymbol, t -> t.instantiate(env));
				final Type result = (Type) value;
				return result;
			} else {
				throw new UnsupportedOperationException();
			}
		}

		@Override
		public Type visitExpressionIndex(final ExpressionIndexContext ctx) {
			final XtaExpression expression = new XtaExpression(scope, ctx.fExpression);
			final Expr<?> expr = expression.instantiate(env);
			final IntLitExpr elemCount = (IntLitExpr) expr;
			final Type result = RangeType.Range(0, elemCount.getValue().intValue() - 1);
			return result;
		}

	}

}
