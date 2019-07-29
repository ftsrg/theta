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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.TypeContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.VariableIdContext;
import hu.bme.mit.theta.xta.utils.ChanType;
import hu.bme.mit.theta.xta.utils.ClockType;
import hu.bme.mit.theta.xta.utils.LabelExpr;
import hu.bme.mit.theta.xta.utils.RangeType;

final class XtaVariableSymbol implements Symbol {

	private final String name;
	private final boolean constant;
	private final boolean broadcast;

	private final XtaType type;
	private final XtaInitialiser initialiser;

	public XtaVariableSymbol(final Scope scope, final TypeContext typeContext,
							 final VariableIdContext variableIdcontext) {
		checkNotNull(typeContext);
		checkNotNull(variableIdcontext);
		name = variableIdcontext.fArrayId.fId.getText();
		constant = (typeContext.fTypePrefix.fConst != null);
		broadcast = (typeContext.fTypePrefix.fBroadcast != null);
		type = new XtaType(scope, typeContext, variableIdcontext.fArrayId.fArrayIndexes);
		initialiser = variableIdcontext.fInitialiser != null ? new XtaInitialiser(scope, variableIdcontext.fInitialiser)
				: null;

		checkArgument(constant || initialiser == null, "Initialisers are only supported for constants");
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isConstant() {
		return constant;
	}

	public Expr<?> instantiate(final String prefix, final Env env) {
		final Type varType = type.instantiate(env);

		if (broadcast && varType != ChanType.getInstance()) {
			throw new UnsupportedOperationException("Keyword \"broadcast\" is only supported for type \"chan\"");
		}

		if (!isSupportedType(varType)) {
			throw new UnsupportedOperationException(varType + " is not supported for variables");
		}

		if (constant) {
			final Expr<?> expr = initialiser.instantiate(varType, env);
			return expr;
		} else {
			if (varType instanceof ClockType) {
				return Decls.Var(prefix + name, Rat()).getRef();
			} else if (isChanArrayType(varType)) {
				final List<Type> args = extractArgs(varType);
				final Label label = Label.of(prefix + name, args, broadcast);
				return LabelExpr.of(label);
			} else {
				return Decls.Var(prefix + name, varType).getRef();
			}
		}
	}

	private static boolean isSupportedType(final Type type) {
		if (type instanceof BoolType) {
			return true;
		} else if (type instanceof IntType) {
			return true;
		} else if (type instanceof ClockType) {
			return true;
		} else if (isChanArrayType(type)) {
			return true;
		} else {
			return false;
		}
	}

	private static boolean isChanArrayType(final Type type) {
		if (type instanceof ChanType) {
			return true;
		} else if (type instanceof ArrayType) {
			final ArrayType<?, ?> arrayType = (ArrayType<?, ?>) type;
			final Type indexType = arrayType.getIndexType();
			final Type elemType = arrayType.getElemType();

			if (!(indexType instanceof BoolType || indexType instanceof RangeType)) {
				return false;
			} else if (elemType instanceof ChanType) {
				return true;
			} else if (elemType instanceof ArrayType) {
				return isChanArrayType(elemType);
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

	private static List<Type> extractArgs(final Type type) {
		if (type instanceof ChanType) {
			return ImmutableList.of();
		} else if (type instanceof ArrayType) {
			final ArrayType<?, ?> arrayType = (ArrayType<?, ?>) type;
			final Type indexType = arrayType.getIndexType();
			final Type elemType = arrayType.getElemType();

			final Type newIndexType = (indexType instanceof RangeType) ? Int() : indexType;

			final List<Type> result = ImmutableList.<Type>builder().add(newIndexType).addAll(extractArgs(elemType))
					.build();
			return result;
		} else {
			throw new AssertionError();
		}
	}

}
