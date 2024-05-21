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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.CompoundInitialiserContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.InitialiserContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.SimpleInitialiserContext;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

final class XtaInitialiser {

	private final Scope scope;
	private final InitialiserContext context;

	public XtaInitialiser(final Scope scope, final InitialiserContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public Expr<?> instantiate(final Type type, final Env env) {
		final InitialiserInstantiationVisitor visitor = new InitialiserInstantiationVisitor(env);
		Expr<?> expr = context.accept(visitor);
		if(type instanceof BoolType){
			if(expr instanceof IntLitExpr){
				if(((IntLitExpr) expr).getValue().intValue() <= 0) expr = BoolLitExpr.of(false);
				else expr = BoolLitExpr.of(true);
			}
		}
		checkArgument(expr.getType().equals(type));
		return expr;
	}

	private final class InitialiserInstantiationVisitor extends XtaDslBaseVisitor<Expr<?>> {
		private final Env env;

		public InitialiserInstantiationVisitor(final Env env) {
			this.env = checkNotNull(env);
		}

		@Override
		public Expr<?> visitSimpleInitialiser(final SimpleInitialiserContext ctx) {
			final XtaExpression expression = new XtaExpression(scope, ctx.fExpression);
			final Expr<?> expr = expression.instantiate(env);
			return expr;
		}

		@Override
		public Expr<?> visitCompoundInitialiser(final CompoundInitialiserContext ctx) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

	}

}
