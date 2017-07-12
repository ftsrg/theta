package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.List;

import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.xta.ChanType;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ArrayIndexContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.BasicTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.BoolTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ChanTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ClockTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ExpressionIndexContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.IdIndexContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.IntTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.RangeTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.RefTypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.TypeContext;
import hu.bme.mit.theta.formalism.xta.utils.ClockType;
import hu.bme.mit.theta.formalism.xta.utils.RangeType;

final class XtaType {

	private final Scope scope;

	private final TypeContext typeContext;
	private final List<ArrayIndexContext> arrayIndexContexts;

	public XtaType(final Scope scope, final TypeContext typeContext, final List<ArrayIndexContext> arrayIndexContexts) {
		this.scope = checkNotNull(scope);
		this.typeContext = checkNotNull(typeContext);
		this.arrayIndexContexts = checkNotNull(arrayIndexContexts);

		checkArgument(typeContext.fTypePrefix.fBroadcast == null);
		checkArgument(typeContext.fTypePrefix.fUrgent == null);
	}

	public Type instantiate(final Environment env) {
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

	private Type createBasicType(final TypeContext typeContext, final Environment env) {
		final BasicTypeInstantiationVisitor visitor = new BasicTypeInstantiationVisitor(env);
		final BasicTypeContext basicTypeContext = typeContext.fBasicType;
		final Type basicType = basicTypeContext.accept(visitor);
		return basicType;
	}

	private Type createIndexType(final ArrayIndexContext arrayIndexContext, final Environment env) {
		final IndexTypeInstantiationVisitor visitor = new IndexTypeInstantiationVisitor(env);
		final Type indexType = arrayIndexContext.accept(visitor);
		return indexType;
	}

	////

	private final class BasicTypeInstantiationVisitor extends XtaDslBaseVisitor<Type> {
		private final Environment env;

		private BasicTypeInstantiationVisitor(final Environment env) {
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

			final int lower = lowerLitExpr.getValue();
			final int upper = upperLitExpr.getValue();

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
		private final Environment env;

		public IndexTypeInstantiationVisitor(final Environment env) {
			this.env = env;
		}

		@Override
		public Type visitIdIndex(final IdIndexContext ctx) {
			final Symbol symbol = scope.resolve(ctx.fId.getText()).get();
			if (symbol instanceof XtaVariableSymbol) {
				final XtaVariableSymbol variableSymbol = (XtaVariableSymbol) symbol;

				assert variableSymbol.isConstant();
				final Object value = env.compute(variableSymbol, v -> v.instantiate("", env));

				final IntLitExpr elemCount = (IntLitExpr) value;
				final Type result = RangeType.Range(0, elemCount.getValue() - 1);
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
			final Type result = RangeType.Range(0, elemCount.getValue() - 1);
			return result;
		}

	}

}
