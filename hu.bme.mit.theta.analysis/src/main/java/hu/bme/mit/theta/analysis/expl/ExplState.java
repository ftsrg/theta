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
package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class ExplState implements ExprState, Valuation {

	private ExplState() {
	}

	public static ExplState create(final Valuation val) {
		if (val.getDecls().isEmpty()) {
			return createTop();
		}
		return new NonBottom(val);
	}

	public static ExplState createBottom() {
		return BottomLazyHolder.INSTANCE;
	}

	public static ExplState createTop() {
		return TopLazyHolder.INSTANCE;
	}

	public abstract boolean isLeq(final ExplState that);

	public abstract boolean isBottom();

	public abstract boolean isTop();

	////

	private static final class NonBottom extends ExplState {

		private static final int HASH_SEED = 6659;
		private final Valuation val;
		private volatile int hashCode;

		private NonBottom(final Valuation val) {
			this.val = checkNotNull(val);
		}

		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return val.getDecls();
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			return val.eval(decl);
		}

		@Override
		public Expr<BoolType> toExpr() {
			return val.toExpr();
		}

		////

		@Override
		public boolean isLeq(final ExplState that) {
			if (that.isBottom()) {
				return false;
			}
			if (that.getDecls().size() > this.getDecls().size()) {
				return false;
			}
			for (final Decl<?> varDecl : that.getDecls()) {
				if (!this.getDecls().contains(varDecl) || !that.eval(varDecl).get().equals(this.eval(varDecl).get())) {
					return false;
				}
			}
			return true;
		}

		@Override
		public boolean isBottom() {
			return false;
		}

		@Override
		public boolean isTop() {
			return val.getDecls().isEmpty();
		}

		////

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + val.hashCode();
				hashCode = result;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof NonBottom) {
				final NonBottom that = (NonBottom) obj;
				return this.val.equals(that.val);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			final ToStringBuilder builder = Utils.toStringBuilder(ExplState.class.getSimpleName());
			for (final Decl<?> varDecl : val.getDecls()) {
				builder.add(varDecl.getName() + " = " + eval(varDecl).get());
			}
			return builder.toString();
		}
	}

	private static final class Bottom extends ExplState {
		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return Collections.emptySet();
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			return Optional.empty();
		}

		@Override
		public Expr<BoolType> toExpr() {
			return BoolExprs.False();
		}

		////

		@Override
		public boolean isLeq(final ExplState that) {
			return true;
		}

		@Override
		public boolean isBottom() {
			return true;
		}

		@Override
		public boolean isTop() {
			return false;
		}

		////

		@Override
		public int hashCode() {
			return 3931;
		}

		@Override
		public boolean equals(final Object obj) {
			return obj instanceof Bottom;
		}

		@Override
		public String toString() {
			return Utils.toStringBuilder(ExplState.class.getSimpleName()).add("Bottom").toString();
		}
	}

	private static class BottomLazyHolder {
		static final ExplState INSTANCE = new Bottom();
	}

	private static class TopLazyHolder {
		static final ExplState INSTANCE = new NonBottom(BasicValuation.empty());
	}
}
