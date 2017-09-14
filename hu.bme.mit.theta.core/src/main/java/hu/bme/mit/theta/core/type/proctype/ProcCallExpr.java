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

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;

public final class ProcCallExpr<ReturnType extends Type> implements Expr<ReturnType> {

	private final static int HASH_SEED = 1471;
	private volatile int hashCode = 0;

	private final Expr<ProcType<ReturnType>> proc;
	private final List<Expr<?>> params;

	ProcCallExpr(final Expr<ProcType<ReturnType>> proc, final Iterable<? extends Expr<?>> params) {
		// TODO Type checking!
		this.proc = checkNotNull(proc);
		this.params = ImmutableList.copyOf(checkNotNull(params));
	}

	public final Expr<ProcType<ReturnType>> getProc() {
		return proc;
	}

	public final List<Expr<?>> getParams() {
		return params;
	}

	@Override
	public final ReturnType getType() {
		return getProc().getType().getReturnType();
	}

	@Override
	public LitExpr<ReturnType> eval(final Valuation val) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int getArity() {
		return params.size();
	}

	@Override
	public List<Expr<?>> getOps() {
		return params;
	}

	@Override
	public Expr<ReturnType> withOps(final List<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + proc.hashCode();
			result = 31 * result + params.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProcCallExpr<?>) {
			final ProcCallExpr<?> that = (ProcCallExpr<?>) obj;
			return this.getProc().equals(that.getProc()) && this.getParams().equals(that.getParams());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return Utils.toStringBuilder("Call").add(proc).addAll(params).toString();
	}

}
