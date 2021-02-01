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
package hu.bme.mit.theta.sts.parser;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.Function;

import com.google.common.primitives.Ints;

import hu.bme.mit.theta.common.parser.SExpr;
import hu.bme.mit.theta.common.parser.SExpr.SAtom;
import hu.bme.mit.theta.common.parser.SExpr.SList;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.parser.CoreInterpreter;
import hu.bme.mit.theta.core.parser.Env;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.STS.Builder;

final class StsInterpreter {

	private final Env env;
	private final CoreInterpreter interpreter;

	public StsInterpreter(final Env env) {
		this.env = checkNotNull(env);
		interpreter = new CoreInterpreter(env);
		initEnv();
	}

	private void initEnv() {
		interpreter.defineCommonTypes();
		interpreter.defineCommonExprs();
		interpreter.defineExpr("prime", interpreter.exprUnaryOperator(PrimeExpr::of));
		env.define("system", stsCreator());
		env.define("var", varCreator());
		env.define("init", stsExprCreator(Context.INIT));
		env.define("invar", stsExprCreator(Context.INVAR));
		env.define("trans", stsExprCreator(Context.TRANS));
		env.define("prop", stsExprCreator(Context.PROP));
	}

	public STS sts(final SExpr sexpr) {
		return (STS) eval(sexpr);
	}

	private Object eval(final SExpr sexpr) {
		if (sexpr.isAtom()) {
			return evalAtom(sexpr.asAtom());
		} else if (sexpr.isList()) {
			return evalList(sexpr.asList());
		} else {
			throw new AssertionError();
		}
	}

	private Object evalAtom(final SAtom satom) {
		final String symbol = satom.getAtom();
		final Integer integer = Ints.tryParse(symbol);
		if (integer != null) {
			return integer;
		} else {
			final Object value = env.eval(symbol);
			return value;
		}
	}

	private Object evalList(final SList slist) {
		final List<SExpr> list = slist.getList();
		final SExpr head = head(list);
		final List<SExpr> tail = tail(list);
		if (head.isAtom()) {
			final String symbol = head.asAtom().getAtom();
			final Object object = env.eval(symbol);
			@SuppressWarnings("unchecked") final Function<List<SExpr>, ?> interpretation = (Function<List<SExpr>, ?>) object;
			final Object value = interpretation.apply(tail);
			return value;
		} else if (head.isList()) {
			throw new UnsupportedOperationException();
		} else {
			throw new AssertionError();
		}
	}

	private Function<List<SExpr>, STS> stsCreator() {
		return sexprs -> {
			final Builder builder = STS.builder();
			env.push();
			for (final SExpr sexpr : sexprs) {
				final Object object = eval(sexpr);
				if (object instanceof VarDecl) {
					final VarDecl<?> varDecl = (VarDecl<?>) object;
					env.define(varDecl.getName(), varDecl);
				} else if (object instanceof ExprContext) {
					final ExprContext exprContext = (ExprContext) object;
					exprContext.apply(builder);
				} else {
					throw new UnsupportedOperationException();
				}
			}
			env.pop();
			return builder.build();
		};
	}

	private Function<List<SExpr>, VarDecl<?>> varCreator() {
		return sexprs -> {
			checkArgument(sexprs.size() == 2);
			final String name = sexprs.get(0).asAtom().getAtom();
			final Type type = interpreter.type(sexprs.get(1));
			final VarDecl<?> varDecl = Var(name, type);
			return varDecl;
		};
	}

	private Function<List<SExpr>, ExprContext> stsExprCreator(final Context context) {
		return sexprs -> {
			checkArgument(sexprs.size() == 1);
			final Expr<?> expr = interpreter.expr(sexprs.get(0));
			return ExprContext.of(context, expr);
		};
	}

	private static final class ExprContext {
		private final Context context;
		private final Expr<BoolType> expr;

		private ExprContext(final Context context, final Expr<?> expr) {
			this.context = checkNotNull(context);
			this.expr = cast(checkNotNull(expr), Bool());
		}

		public static ExprContext of(final Context context, final Expr<?> expr) {
			return new ExprContext(context, expr);
		}

		public void apply(final STS.Builder builder) {
			context.apply(builder, expr);
		}
	}

	private enum Context {
		INIT((b, e) -> b.addInit(e)),

		INVAR((b, e) -> b.addInvar(e)),

		TRANS((b, e) -> b.addTrans(e)),

		PROP((b, e) -> b.setProp(e));

		private final BiConsumer<Builder, Expr<BoolType>> consumer;

		private Context(final BiConsumer<Builder, Expr<BoolType>> consumer) {
			this.consumer = checkNotNull(consumer);
		}

		public void apply(final STS.Builder builder, final Expr<BoolType> expr) {
			consumer.accept(builder, expr);
		}
	}

}
