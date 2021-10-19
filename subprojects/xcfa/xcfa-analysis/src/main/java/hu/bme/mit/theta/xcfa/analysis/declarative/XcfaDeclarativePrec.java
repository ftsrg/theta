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
package hu.bme.mit.theta.xcfa.analysis.declarative;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer.replaceVars;

public final class XcfaDeclarativePrec<P extends Prec> implements Prec {
	private final P globalPrec;
	private final Map<VarDecl<?>, List<VarDecl<?>>> globalToLocal;

	private XcfaDeclarativePrec(final P globalPrec, Map<VarDecl<?>, List<VarDecl<?>>> globalToLocal) {
		this.globalPrec = globalPrec;
		this.globalToLocal = globalToLocal;
	}

	public static <P extends Prec> XcfaDeclarativePrec<P> create(final P globalPrec, Map<VarDecl<?>, List<VarDecl<?>>> globalToLocal) {

		return new XcfaDeclarativePrec<P>(globalPrec, globalToLocal);
	}

	public static XcfaDeclarativePrec<PredPrec> collectAssumes(XCFA xcfa) {
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
		return XcfaDeclarativePrec.create(PredPrec.of(assumes), getGlobalToLocal(xcfa));
	}

	public static Map<VarDecl<?>, List<VarDecl<?>>> getGlobalToLocal(XCFA xcfa) {
		Map<VarDecl<?>, List<VarDecl<?>>> ret = new LinkedHashMap<>();
		for (VarDecl<? extends Type> globalVar : xcfa.getGlobalVars()) {
			final List<VarDecl<?>> list = new ArrayList<>();
			ret.put(globalVar, list);
			final VarDecl<?> localCopy = Var(globalVar.getName() + "_local", globalVar.getType());
			for (XcfaProcess process : xcfa.getProcesses()) {
				for (VarDecl<?> localVar : process.getThreadLocalVars()) {
					if(localVar.getName().startsWith(localCopy.getName()) && localVar.getType().equals(localCopy.getType())) {
						list.add(localVar);
					}
				}
				for (XcfaProcedure procedure : process.getProcedures()) {
					for (VarDecl<?> localVar : procedure.getLocalVars()) {
						if(localVar.getName().startsWith(localCopy.getName()) && localVar.getType().equals(localCopy.getType())) {
							list.add(localVar);
						}
					}
				}
			}
		}
		return ret;
	}

	public P getGlobalPrec() {
		return globalPrec;
	}

	public XcfaDeclarativePrec<P> refine(P runningPrec) {
//		if(runningPrec.getUsedVars().stream().anyMatch(globalToLocal::containsKey)) {
//			runningPrec = expandPrec(runningPrec);
//		}
		if (this.globalPrec.equals(runningPrec)) {
			return this;
		} else {
			return create(runningPrec, globalToLocal);
		}
	}

	private P expandPrec(P runningPrec) {
		if(runningPrec instanceof PredPrec) {
			List<Expr<BoolType>> newPreds = new ArrayList<>();
			for (Expr<BoolType> pred : ((PredPrec) runningPrec).getPreds()) {
				final Set<VarDecl<?>> vars = ExprUtils.getVars(pred);
				if(vars.stream().anyMatch(globalToLocal::containsKey)) {
					final List<Map.Entry<VarDecl<?>, List<VarDecl<?>>>> entries = globalToLocal.entrySet().stream().filter(e -> vars.contains(e.getKey())).collect(Collectors.toList());
					final List<List<Decl<?>>> product = Lists.cartesianProduct(entries.stream().map(Map.Entry::getValue).collect(Collectors.toList()));
					for (List<Decl<?>> decls : product) {
						Map<Decl<?>, Decl<?>> lut = new LinkedHashMap<>();
						for (int i = 0; i < decls.size(); i++) {
							lut.put(entries.get(i).getKey(), decls.get(i));
						}
						newPreds.add(replaceVars(pred, lut));
					}
				} else {
					newPreds.add(pred);
				}
			}
			return (P)PredPrec.of(newPreds);
		} else if (runningPrec instanceof ExplPrec) {
			final Set<VarDecl<?>> vars = new LinkedHashSet<>(((ExplPrec) runningPrec).getVars());
			for (VarDecl<?> var : ((ExplPrec) runningPrec).getVars()) {
				vars.addAll(globalToLocal.getOrDefault(var, List.of()));
			}
			return (P) ExplPrec.of(vars);
		}
		throw new UnsupportedOperationException("Pred type not yet supported: " + runningPrec.getClass().getSimpleName());
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		XcfaDeclarativePrec<?> xcfaPrec = (XcfaDeclarativePrec<?>) o;
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
