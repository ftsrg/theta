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
package hu.bme.mit.theta.xcfa.analysis.declarative.noota.prec;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.FrontendMetadata;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

public final class XcfaDeclPrec<P extends Prec> implements Prec {
	private final P globalPrec;
	private final Set<VarDecl<?>> trackedVariables;

	private XcfaDeclPrec(final P globalPrec) {
		this.globalPrec = globalPrec;
		trackedVariables = new LinkedHashSet<>();
		for (VarDecl<?> usedVar : this.globalPrec.getUsedVars()) {
			final Optional<Object> globalopt = FrontendMetadata.getMetadataValue(usedVar, "sourceGlobal");
			globalopt.ifPresent(o -> trackedVariables.add((VarDecl<?>) o));
		}
	}

	public static <P extends Prec> XcfaDeclPrec<P> create(final P globalPrec) {
//		if(globalPrec instanceof PredPrec) {
//			Collection<Expr<BoolType>> newPreds = new ArrayList<>();
//			for (Expr<BoolType> pred : ((PredPrec) globalPrec).getPreds()) {
//				final Set<VarDecl<?>> vars = getVars(pred).stream()
//						.filter(varDecl -> FrontendMetadata.getMetadataValue(varDecl, "sourceGlobal").isPresent()).collect(Collectors.toSet());
//				if(vars.size() > 0) {
//					checkState(vars.size() == 1, "Algorithm not yet implemented for multi-variable predicates");
//					final VarDecl<?> local = vars.stream().findAny().get();
//					final Set<Object> localVars = FrontendMetadata.lookupMetadata("sourceGlobal", FrontendMetadata.getMetadataValue(local, "sourceGlobal").get());
//					for (Object localVar : localVars) {
//						final Map<VarDecl<?>, VarDecl<?>> lut = Map.of(local, (VarDecl<?>) localVar);
//						newPreds.add(replaceVars(pred, lut));
//					}
//				} else newPreds.add(pred);
//			}
//			return new XcfaDeclPrec<>((P)PredPrec.of(newPreds));
//		} else if (globalPrec instanceof ExplPrec) {
//			final Set<VarDecl<?>> newVars = new LinkedHashSet<>(((ExplPrec) globalPrec).getVars());
//			final Set<VarDecl<?>> vars = ((ExplPrec) globalPrec).getVars();
//			for (VarDecl<?> var : vars) {
//				final Optional<Object> sourceGlobal = FrontendMetadata.getMetadataValue(var, "sourceGlobal");
//				if(sourceGlobal.isPresent()) {
//					for (Object local : FrontendMetadata.lookupMetadata("sourceGlobal", sourceGlobal)) {
//						newVars.add((VarDecl<?>) local);
//					}
//				}
//			}
//			return new XcfaDeclPrec<P>((P)ExplPrec.of(newVars));
//		}
		return new XcfaDeclPrec<P>(globalPrec);
	}

	public P getGlobalPrec() {
		return globalPrec;
	}

	public XcfaDeclPrec<P> refine(P runningPrec) {
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
		XcfaDeclPrec<?> xcfaPrec = (XcfaDeclPrec<?>) o;
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
		return "XcfaDeclPrec{" +
				"globalPrec=" + globalPrec +
				"trackedVars=" + trackedVariables +
				'}';
	}

	public Set<VarDecl<?>> getTrackedVariables() {
		return trackedVariables;
	}
}
