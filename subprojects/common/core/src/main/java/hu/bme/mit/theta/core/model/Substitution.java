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
package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

/**
 * Interface for a substitution, which is a mapping from declarations to expressions.
 */
public interface Substitution {

	/**
	 * Get all the declarations for which an expression is assigned.
	 * @return
	 */
	Collection<? extends Decl<?>> getDecls();

	/**
	 * Evaluate a declaration, i.e., get the corresponding expression.
	 * @param decl
	 * @param <DeclType>
	 * @return
	 */
	<DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl);

	default <T extends Type> Expr<T> apply(final Expr<T> expr) {
		if (expr instanceof RefExpr) {
			final RefExpr<T> ref = (RefExpr<T>) expr;
			final Decl<T> decl = ref.getDecl();
			final Optional<? extends Expr<T>> optSub = eval(decl);
			if (optSub.isPresent()) {
				final Expr<T> sub = optSub.get();
				return sub;
			} else {
				return expr;
			}
		} else {
			return expr.map(this::apply);
		}
	}
}
