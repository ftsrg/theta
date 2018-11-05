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
package hu.bme.mit.theta.core.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class ParamBinding implements Substitution {

	private final List<ParamDecl<?>> params;
	private final Map<Decl<?>, Expr<?>> paramToArg;

	public ParamBinding(final List<? extends ParamDecl<?>> params, final List<? extends Expr<?>> args) {
		checkNotNull(params);
		checkNotNull(args);
		checkArgument(params.size() == args.size());

		this.params = ImmutableList.copyOf(params);
		this.paramToArg = new HashMap<>();

		for (int i = 0; i < params.size(); i++) {
			final ParamDecl<?> param = params.get(i);
			final Expr<?> arg = args.get(i);
			checkArgument(arg.getType().equals(param.getType()));
			paramToArg.put(param, arg);
		}
	}

	public static ParamBinding create(final List<? extends ParamDecl<?>> params, final List<? extends Expr<?>> args) {
		return new ParamBinding(params, args);
	}

	////

	@Override
	public Collection<ParamDecl<?>> getDecls() {
		return params;
	}

	@Override
	public <DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl) {
		@SuppressWarnings("unchecked")
		final Expr<DeclType> value = (Expr<DeclType>) paramToArg.get(decl);
		return Optional.ofNullable(value);
	}
}
