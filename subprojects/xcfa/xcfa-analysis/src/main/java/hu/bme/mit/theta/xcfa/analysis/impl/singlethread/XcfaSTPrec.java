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
package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.Collection;
import java.util.Objects;
import java.util.Set;

public final class XcfaSTPrec<P extends Prec> implements Prec {
	private final P globalPrec;

	private XcfaSTPrec(final P globalPrec) {
		this.globalPrec = globalPrec;
	}

	public static <P extends Prec> XcfaSTPrec<P> create(final P globalPrec) {
		return new XcfaSTPrec<P>(globalPrec);
	}

	public static XcfaSTPrec<PredPrec> collectAssumes(XCFA xcfa) {
		Set<Expr<BoolType>> assumes = Containers.createSet();
		for (XcfaProcess process : xcfa.getProcesses()) {
			for (XcfaProcedure procedure : process.getProcedures()) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (XcfaLabel label : edge.getLabels()) {
						if (label instanceof XcfaLabel.StmtXcfaLabel && label.getStmt() instanceof AssumeStmt) {
							AssumeStmt assumeStmt = (AssumeStmt)label.getStmt();
							assumes.add(ExprUtils.ponate(assumeStmt.getCond()));
						}
					}
				}
			}
		}
		return XcfaSTPrec.create(PredPrec.of(assumes));
	}

	public P getGlobalPrec() {
		return globalPrec;
	}

	public XcfaSTPrec<P> refine(P runningPrec) {
		if (this.globalPrec.equals(runningPrec)) {
			return this;
		} else {
			return create(runningPrec);
		}
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaSTPrec<?> xcfaPrec = (XcfaSTPrec<?>) o;
		return Objects.equals(globalPrec, xcfaPrec.globalPrec);
	}

	@Override
	public int hashCode() {
		return Objects.hash(globalPrec);
	}

	@Override
	public Collection<VarDecl<?>> getUsedVars() {
		return globalPrec.getUsedVars();
	}

	@Override
	public String toString() {
		return globalPrec.toString();
	}
}
