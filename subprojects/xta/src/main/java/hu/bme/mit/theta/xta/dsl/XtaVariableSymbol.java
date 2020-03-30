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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.TypeContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.VariableIdContext;
import hu.bme.mit.theta.xta.utils.ChanType;
import hu.bme.mit.theta.xta.utils.ClockType;
import hu.bme.mit.theta.xta.utils.RangeType;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

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
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isConstant() {
		return constant;
	}

	public boolean isBroadcast() {
		return broadcast;
	}

	public InstantiateResult instantiate(final String prefix, final Env env) {
		final Type varType = type.instantiate(env);

		if (varType == ChanType.getInstance() && initialiser != null) {
			throw new UnsupportedOperationException("Initialisers are not supported for type \"chan\"");
		}

		if (constant) {
			if (!isSupportedDataType(varType)) {
				throw new UnsupportedOperationException("Unsupported type for const " + name + ".");
			} else if (initialiser == null) {
				throw new UnsupportedOperationException("The value of const " + name + " is undefined.");
			} else {
				final LitExpr<?> expr = (LitExpr<?>) initialiser.instantiate(varType, env);
				return InstantiateResult.constant(expr);
			}
		} else if (isSupportedDataType(varType)) {
			if (broadcast) {
				throw new UnsupportedOperationException("Unsupported keyword \"broadcast\" for variable" + name + ".");
			} else {
				final VarDecl<?> varDecl = Decls.Var(prefix + name, varType);
				final LitExpr<?> initValue;
				if (initialiser != null) {
					final Expr<?> expr = initialiser.instantiate(varType, env);
					if (expr instanceof LitExpr) {
						initValue = (LitExpr<?>) expr;
					} else {
						throw new AssertionError();
					}
				} else {
					initValue = defaultValueFor(varType);
				}
				return InstantiateResult.dataVariable(varDecl, initValue);
			}
		} else if (varType instanceof ClockType) {
			if (broadcast) {
				throw new UnsupportedOperationException("Unsupported keyword \"broadcast\" for variable" + name + ".");
			} else if (initialiser != null) {
				throw new UnsupportedOperationException("Clock " + name + " should not be initialized.");
			} else {
				final VarDecl<RatType> varDecl = Decls.Var(prefix + name, Rat());
				return InstantiateResult.clockVariable(varDecl);
			}
		} else if (isChanArrayType(varType)) {
			final List<Type> args = extractArgs(varType);
			final Label label = Label.of(prefix + name, args, broadcast);
			return InstantiateResult.channel(label);
		} else {
			throw new UnsupportedOperationException("Type of variable " + name + " is unsupported.");
		}
	}

	private static boolean isSupportedDataType(Type type) {
		return type instanceof BoolType || type instanceof IntType;
	}

	private static <T extends Type> LitExpr<T> defaultValueFor(final T type) {
		checkArgument(isSupportedDataType(type));
		if (type instanceof BoolType) {
			return (LitExpr<T>) cast(False(), type);
		} else if (type instanceof IntType) {
			return (LitExpr<T>) cast(Int(0), type);
		} else {
			throw new AssertionError();
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

	public static abstract class InstantiateResult {

		private InstantiateResult() {
		}

		public static InstantiateResult constant(final LitExpr<?> expr) {
			return new Constant(expr);
		}

		public static InstantiateResult clockVariable(final VarDecl<RatType> varDecl) {
			return new ClockVariable(varDecl);
		}

		public static InstantiateResult dataVariable(final VarDecl<?> varDecl, final LitExpr<?> initValue) {
			return new DataVariable(varDecl, initValue);
		}

		public static InstantiateResult channel(final Label label) {
			return new Channel(label);
		}

		public boolean isDataVariable() {
			return false;
		}

		public boolean isClockVariable() {
			return false;
		}

		public boolean isConstant() {
			return false;
		}

		public boolean isChannel() {
			return false;
		}

		public DataVariable asDataVariable() {
			throw new ClassCastException();
		}

		public ClockVariable asClockVariable() {
			throw new ClassCastException();
		}

		public Constant asConstant() {
			throw new ClassCastException();
		}

		public Channel asChannel() {
			throw new ClassCastException();
		}
	}


	public static final class DataVariable extends InstantiateResult {
		private final VarDecl<?> varDecl;
		private final LitExpr<?> initValue;

		private DataVariable(final VarDecl<?> varDecl, LitExpr<?> litExpr) {
			this.varDecl = checkNotNull(varDecl);
			this.initValue = checkNotNull(litExpr);
		}

		@Override
		public boolean isDataVariable() {
			return true;
		}

		@Override
		public DataVariable asDataVariable() {
			return this;
		}

		public VarDecl<?> getVarDecl() {
			return varDecl;
		}

		public LitExpr<?> getInitValue() {
			return initValue;
		}
	}

	public static final class ClockVariable extends InstantiateResult{
		private final VarDecl<RatType> varDecl;

		private ClockVariable(final VarDecl<RatType> varDecl) {
			this.varDecl = checkNotNull(varDecl);
		}

		@Override
		public boolean isClockVariable() {
			return true;
		}

		@Override
		public ClockVariable asClockVariable() {
			return this;
		}

		public VarDecl<RatType> getVarDecl() {
			return varDecl;
		}
	}

	public static final class Constant extends InstantiateResult {
		private final LitExpr<?> expr;

		private Constant(final LitExpr<?> expr) {
			this.expr = checkNotNull(expr);
			checkArgument(isSupportedDataType(expr.getType()));
		}

		@Override
		public boolean isConstant() {
			return true;
		}

		@Override
		public Constant asConstant() {
			return this;
		}

		public LitExpr<?> getExpr() {
			return expr;
		}
	}

	public static final class Channel extends InstantiateResult {
		private final Label label;

		private Channel(final Label label) {
			this.label = checkNotNull(label);
		}

		@Override
		public boolean isChannel() {
			return true;
		}

		@Override
		public Channel asChannel() {
			return this;
		}

		public Label getLabel() {
			return label;
		}
	}

}
