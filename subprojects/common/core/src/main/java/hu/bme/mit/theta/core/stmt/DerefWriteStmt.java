/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.DeRefExpr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class DerefWriteStmt implements Stmt {
	private static final String STMT_LABEL = "derefwrite";

	private final DeRefExpr<Type> deRef;
	private final Expr<Type> expr;

	private DerefWriteStmt(final DeRefExpr<Type> lhs, final Expr<Type> expr) {
		this.deRef = checkNotNull(lhs);
		this.expr = checkNotNull(expr);
	}

	public static DerefWriteStmt of(final DeRefExpr<?> lhs, final Expr<?> rhs) {
		return new DerefWriteStmt((DeRefExpr<Type>) lhs, (Expr<Type>) rhs);
	}

	public static DerefWriteStmt create(final DeRefExpr<?> lhs, final Expr<?> rhs) {
		@SuppressWarnings("unchecked") final DeRefExpr<?> newLhs = (DeRefExpr<?>) lhs;
		final Expr<?> newRhs = cast(rhs, newLhs.getType());
		return DerefWriteStmt.of(newLhs, newRhs);
	}

	public DeRefExpr<Type> getDeRef() {
		return deRef;
	}

	public Expr<Type> getExpr() {
		return expr;
	}

	@Override
	public String toString() {
		return STMT_LABEL + "(" + deRef + ", " + expr + ")";
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
