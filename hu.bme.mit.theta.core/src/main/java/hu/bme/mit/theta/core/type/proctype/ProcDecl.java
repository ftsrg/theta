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
package hu.bme.mit.theta.core.type.proctype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.proctype.ProcExprs.Proc;
import static java.util.stream.Collectors.toList;

import java.util.List;
import java.util.stream.Stream;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.AbstractDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;

public final class ProcDecl<ReturnType extends Type> extends AbstractDecl<ProcType<ReturnType>> {

	private final String name;
	private final List<ParamDecl<? extends Type>> paramDecls;
	private final ReturnType returnType;
	private final ProcType<ReturnType> type;

	ProcDecl(final String name, final List<? extends ParamDecl<? extends Type>> paramDecls,
			final ReturnType returnType) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkArgument(name.length() > 0);
		this.name = name;
		this.paramDecls = ImmutableList.copyOf(paramDecls);
		this.returnType = returnType;

		type = createProcType(paramDecls, returnType);
	}

	private static <ReturnType extends Type> ProcType<ReturnType> createProcType(
			final List<? extends ParamDecl<? extends Type>> paramDecls, final ReturnType returnType) {
		final Stream<Type> paramTypeStream = paramDecls.stream().map(ParamDecl::getType);
		final List<Type> paramTypes = paramTypeStream.collect(toList());
		return Proc(paramTypes, returnType);
	}

	@Override
	public String getName() {
		return name;
	}

	public List<? extends ParamDecl<?>> getParamDecls() {
		return paramDecls;
	}

	public ReturnType getReturnType() {
		return returnType;
	}

	@Override
	public ProcType<ReturnType> getType() {
		return type;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Proc(");
		sb.append(name);
		for (final ParamDecl<?> paramDecl : paramDecls) {
			sb.append(", ");
			sb.append(paramDecl);
		}
		sb.append(" : ");
		sb.append(returnType);
		return sb.toString();
	}

}
