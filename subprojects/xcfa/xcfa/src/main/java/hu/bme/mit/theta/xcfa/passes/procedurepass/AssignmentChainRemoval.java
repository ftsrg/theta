/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.FenceStmt;
import hu.bme.mit.theta.core.stmt.xcfa.JoinThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.XcfaStmtUtils;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.Skip;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

/**
 * Currently, this pass is not used due to performance issues. However, a similar one could be useful.
 */
public class AssignmentChainRemoval extends ProcedurePass {

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		Map<VarDecl<?>, Set<Tuple2<XcfaEdge, Stmt>>> rhsUsages = new LinkedHashMap<>();
		Map<VarDecl<?>, Set<Tuple2<XcfaEdge, Stmt>>> lhsUsages = new LinkedHashMap<>();
		Set<VarDecl<?>> usableVars = new LinkedHashSet<>(builder.getLocalVars().keySet());

		for (XcfaEdge edge : builder.getEdges()) {
			for (Stmt stmt : edge.getStmts()) {
				Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> vars = stmt.accept(new XcfaStmtVisitor<Void, Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>>>() {
					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(XcfaCallStmt stmt, Void param) {
						Set<VarDecl<?>> lhsVars = new LinkedHashSet<>();
						Set<VarDecl<?>> noInlineVars = new LinkedHashSet<>();
						for (Expr<?> stmtParam : stmt.getParams()) {
							if(stmtParam instanceof RefExpr<?>) noInlineVars.add((VarDecl<?>) ((RefExpr<?>) stmtParam).getDecl());
							else lhsVars.addAll(ExprUtils.getVars(stmtParam));
						}
						return Tuple3.of(Optional.empty(), noInlineVars, lhsVars);
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(StoreStmt storeStmt, Void param) {
						return Tuple3.of(Optional.of(storeStmt.getGlobal()), Set.of(), Set.of(storeStmt.getLocal()));
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(LoadStmt loadStmt, Void param) {
						return Tuple3.of(Optional.of(loadStmt.getLocal()), Set.of(), Set.of(loadStmt.getGlobal()));
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(FenceStmt fenceStmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(), Set.of());
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(AtomicBeginStmt atomicBeginStmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(), Set.of());
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(AtomicEndStmt atomicEndStmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(), Set.of());
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(StartThreadStmt startThreadStmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(startThreadStmt.getKey()), ExprUtils.getVars(startThreadStmt.getParam()));
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(JoinThreadStmt joinThreadStmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(joinThreadStmt.getKey()), Set.of());
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(SkipStmt stmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(), Set.of());
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(AssumeStmt stmt, Void param) {
						return Tuple3.of(Optional.empty(), Set.of(), StmtUtils.getVars(stmt));
					}

					@Override
					public <DeclType extends Type> Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(AssignStmt<DeclType> stmt, Void param) {
						return Tuple3.of(Optional.of(stmt.getVarDecl()), Set.of(), ExprUtils.getVars(stmt.getExpr()));
					}

					@Override
					public <DeclType extends Type> Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(HavocStmt<DeclType> stmt, Void param) {
						return Tuple3.of(Optional.of(stmt.getVarDecl()), Set.of(), Set.of());
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(XcfaStmt xcfaStmt, Void param) {
						return xcfaStmt.accept(this, param);
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(SequenceStmt stmt, Void param) {
						throw new UnsupportedOperationException("Not yet supported");
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(NonDetStmt stmt, Void param) {
						throw new UnsupportedOperationException("Not yet supported");
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(OrtStmt stmt, Void param) {
						throw new UnsupportedOperationException("Not yet supported");
					}

					@Override
					public Tuple3<Optional<VarDecl<?>>, Set<VarDecl<?>>, Set<VarDecl<?>>> visit(LoopStmt stmt, Void param) {
						throw new UnsupportedOperationException("Not yet supported");
					}
				}, null);
				Optional<VarDecl<?>> lhsVar = vars.get1();
				Set<VarDecl<?>> nouseVars = vars.get2();
				Set<VarDecl<?>> rhsVars = vars.get3();

				usableVars.removeAll(nouseVars);
				for (VarDecl<?> rhsVar : rhsVars) {
					rhsUsages.putIfAbsent(rhsVar, new LinkedHashSet<>());
					rhsUsages.get(rhsVar).add(Tuple2.of(edge, stmt));
				}
				if(lhsVar.isPresent()) {
					lhsUsages.putIfAbsent(lhsVar.get(), new LinkedHashSet<>());
					lhsUsages.get(lhsVar.get()).add(Tuple2.of(edge, stmt));
				}
			}
		}
		Map<VarDecl<?>, Set<Tuple2<XcfaEdge, Stmt>>> filteredLhsUsages = rhsUsages.entrySet().stream().filter(varDeclSetEntry -> usableVars.contains(varDeclSetEntry.getKey())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		Map<VarDecl<?>, Set<Tuple2<XcfaEdge, Stmt>>> filteredRhsUsages = lhsUsages.entrySet().stream().filter(varDeclSetEntry -> usableVars.contains(varDeclSetEntry.getKey())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));

		boolean found = true;
		while(found) {
			found = false;
			Set<VarDecl<?>> removableVars = filteredRhsUsages.entrySet().stream().filter(varDeclSetEntry -> varDeclSetEntry.getValue().size() == 1 && onlyForwardReachable(varDeclSetEntry.getValue().iterator().next(), new LinkedHashSet<>(filteredLhsUsages.getOrDefault(varDeclSetEntry.getKey(), Set.of())))).map(Map.Entry::getKey).collect(Collectors.toSet());
			if(removableVars.size() > 0) {
				found = true;

				for (VarDecl<?> removableVar : removableVars) {
					Expr<?> newExpr = null;
					boolean isHavoc = false;
					Map<XcfaEdge, XcfaEdge> newEdgeMap = new LinkedHashMap<>();

					for (Tuple2<XcfaEdge, Stmt> lhsEdge : filteredRhsUsages.get(removableVar)) {
						XcfaEdge lhsToRemove = lhsEdge.get1();
						List<Stmt> newStmts = new ArrayList<>();
						for (Stmt stmt : lhsToRemove.getStmts()) {
							if(stmt != lhsEdge.get2()) newStmts.add(stmt);
							else {
								checkState(newExpr == null && !isHavoc, "New expression should not be overwritten!");
								if(stmt instanceof HavocStmt) isHavoc = true;
								else if(stmt instanceof AssignStmt) {
									newExpr = ((AssignStmt<?>) stmt).getExpr();
									FrontendMetadata.create(newExpr, "cType", CComplexType.getType(((AssignStmt<?>) stmt).getVarDecl().getRef()));
								}
								else if(stmt instanceof StoreStmt) newExpr = ((StoreStmt) stmt).getLocal().getRef();
								else if(stmt instanceof LoadStmt) newExpr = ((LoadStmt) stmt).getGlobal().getRef();
								else throw new UnsupportedOperationException("Unknown lhs-modifying stmt: " + stmt);
							}
						}
						XcfaEdge lhsNewEdge = new XcfaEdge(lhsToRemove.getSource(), lhsToRemove.getTarget(), newStmts);
						newEdgeMap.put(lhsToRemove, lhsNewEdge);
					}
					final Expr<?> finalNewExpr = newExpr;

					boolean canInline = true;
					rhsLoop:
					for (Tuple2<XcfaEdge, Stmt> rhsEdge : filteredLhsUsages.getOrDefault(removableVar, Set.of())) {
						XcfaEdge toRemove = rhsEdge.get1();
						List<Stmt> newStmts = new ArrayList<>();
						for (Stmt stmt : toRemove.getStmts()) {
							if(stmt != rhsEdge.get2()) newStmts.add(stmt);
							else {
								if(isHavoc && !(stmt instanceof AssignStmt && (((AssignStmt<?>) stmt).getExpr() instanceof RefExpr))) {
									canInline = false;
									break rhsLoop;
								}
								else if(isHavoc) {
									newStmts.add(Havoc(((AssignStmt<?>) stmt).getVarDecl()));
								}
								else {
									Optional<Stmt> newStmt = XcfaStmtUtils.replaceStmt(stmt, expr -> {
										if (expr instanceof RefExpr && ((RefExpr<Type>) expr).getDecl().equals(removableVar)) {
											CComplexType type = CComplexType.getType(removableVar.getRef());
											return Optional.of(cast(type.castTo(finalNewExpr), removableVar.getType()));
										}
										else return Optional.empty();
									});
									checkState(newStmt.isPresent(), "Rhs var is probably not used on the right side!");
									newStmts.add(newStmt.get());
								}
							}
						}
						newEdgeMap.put(toRemove, new XcfaEdge(toRemove.getSource(), toRemove.getTarget(), newStmts));
					}

					if(canInline) {
						newEdgeMap.forEach((xcfaEdge, xcfaEdge2) -> {
							builder.removeEdge(xcfaEdge);
							builder.addEdge(xcfaEdge2);
						});
					}

					filteredRhsUsages.remove(removableVar);
					filteredLhsUsages.remove(removableVar);

				}
			}

		}
		return builder;
	}

	// on every outgoing path, all reachable `goals` entries are reached before a recursion
	private boolean onlyForwardReachable(Tuple2<XcfaEdge, Stmt> start, Set<Tuple2<XcfaEdge, Stmt>> goals) {
		return onlyForwardReachable(start, start, goals, true, new LinkedHashSet<>());
	}

	private boolean onlyForwardReachable(Tuple2<XcfaEdge, Stmt> start, Tuple2<XcfaEdge, Stmt> current, Set<Tuple2<XcfaEdge, Stmt>> goals, boolean init, Set<Tuple2<XcfaEdge, Stmt>> visited) {
		if(visited.contains(current)) return true;
		visited.add(current);
		if(!init && start.equals(current)) return false;
		goals.remove(current);
		if(goals.size() == 0) return true;

		List<Stmt> stmts = current.get1().getStmts();
		int index = stmts.indexOf(current.get2());
		if(index == stmts.size() - 1) {
			for (XcfaEdge outgoingEdge : current.get1().getTarget().getOutgoingEdges()) {
				Stmt stmt = outgoingEdge.getStmts().size() == 0 ? Skip() : outgoingEdge.getStmts().get(0);
				if(!onlyForwardReachable(start, Tuple2.of(outgoingEdge, stmt), new LinkedHashSet<>(goals), false, new LinkedHashSet<>(visited))) return false;
			}
			return true;
		}
		else return onlyForwardReachable(start, Tuple2.of(current.get1(), stmts.get(index + 1)), goals, false, visited);
	}
}
