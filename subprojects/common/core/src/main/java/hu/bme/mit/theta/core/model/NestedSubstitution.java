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

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

/**
 * Class representing a nested substitution. If a declaration is not present in
 * the actual substitution it is searched in the enclosing substitutions
 * recursively.
 */
public final class NestedSubstitution implements Substitution {

	private final Substitution enclosingSubst;
	private final Substitution subst;

	private NestedSubstitution(final Substitution enclosingSubst, final Substitution subst) {
		this.enclosingSubst = checkNotNull(enclosingSubst);
		this.subst = checkNotNull(subst);
	}

	public static NestedSubstitution create(final Substitution enclosingSubst, final Substitution subst) {
		return new NestedSubstitution(enclosingSubst, subst);
	}

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		final Set<Decl<?>> decls = new HashSet<>();
		decls.addAll(subst.getDecls());
		decls.addAll(enclosingSubst.getDecls());
		return decls;
	}

	@Override
	public <DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl) {
		final Optional<? extends Expr<DeclType>> optExpr = subst.eval(decl);
		if (optExpr.isPresent()) {
			return optExpr;
		} else {
			return enclosingSubst.eval(decl);
		}
	}
}
