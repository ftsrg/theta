package hu.bme.mit.theta.xcfa.passes.procedurepass;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.utils.XcfaStmtUtils.replacesVarsInStmt;

public class Utils {
	public static Set<XcfaEdge> collectReverseEdges(XcfaLocation location) {
		return collectReverseEdges(location, new LinkedHashSet<>(Set.of(location)));
	}

	private static Set<XcfaEdge> collectReverseEdges(XcfaLocation location, Set<XcfaLocation> visited) {
		Set<XcfaEdge> ret = new LinkedHashSet<>();
		List<XcfaEdge> outgoingEdges = new ArrayList<>(location.getOutgoingEdges());
		while(outgoingEdges.size() > 0) {
			ArrayList<XcfaEdge> copy = new ArrayList<>(outgoingEdges);
			outgoingEdges.clear();
			for (XcfaEdge outgoingEdge : copy) {
				if (visited.contains(outgoingEdge.getTarget())) {
					ret.add(outgoingEdge);
				} else {
					visited.add(outgoingEdge.getTarget());
					outgoingEdges.addAll(outgoingEdge.getTarget().getOutgoingEdges());
				}
			}
		}
		return ret;
	}

	/**
	 * This class can be used as a stack while using a Set for fast contains() performance
	 */
	private static class SetStack<T>{
		private final Stack<T> stack = new Stack<>();
		private final Set<T> set = new LinkedHashSet<>();

		public SetStack(SetStack<T> from) {
			from.stack.forEach(this.stack::push); // TODO: does this preserve order?
			set.addAll(from.set);
		}

		public SetStack(){}

		public void push(T t) {
			checkArgument(!set.contains(t), "SetStack can only hold unique elements!");
			stack.push(t);
			set.add(t);
		}
		public T pop() {
			T pop = stack.pop();
			set.remove(pop);
			return pop;
		}
		public T peek() {
			return stack.peek();
		}
		public boolean contains(T t) {
			return set.contains(t);
		}

		public List<T> getList() {
			return stack;
		}
	}

	public static XcfaProcedure.Builder copyBuilder(XcfaProcedure.Builder builder) {
		return getBuilder(builder.getName(), builder.getRetType(), builder.getLocs(), builder.getFinalLoc(), builder.getInitLoc(), builder.getErrorLoc(), builder.getEdges(), builder.getParams(), builder.getLocalVars());
	}

	public static XcfaProcedure.Builder createBuilder(XcfaProcedure proc) {

		return getBuilder(proc.getName(), proc.getRetType(), proc.getLocs(), proc.getFinalLoc(), proc.getInitLoc(), proc.getErrorLoc(), proc.getEdges(), proc.getParams(), proc.getLocalVarMap());
	}

	private static int counter = 0;
	private static XcfaProcedure.Builder getBuilder(String name, Type retType, List<XcfaLocation> locs, XcfaLocation finalLoc, XcfaLocation initLoc, XcfaLocation errorLoc, List<XcfaEdge> edges, Map<VarDecl<?>, XcfaProcedure.Direction> params, Map<VarDecl<?>, Optional<LitExpr<?>>> localVars) {
		XcfaProcedure.Builder ret = XcfaProcedure.builder();
		ret.setName(name);
		ret.setRetType(retType);
		Map<VarDecl<?>, VarDecl<?>> varLut = new LinkedHashMap<>();
		params.forEach((varDecl, direction) -> {
			final VarDecl<?> newVar = Var(varDecl.getName() + "_" + counter++, varDecl.getType());
			if(FrontendMetadata.getMetadataValue(varDecl.getRef(), "cType").isPresent())
				FrontendMetadata.create(newVar.getRef(), "cType", CComplexType.getType(varDecl.getRef()));
			varLut.put(varDecl, newVar);
			ret.createParam(direction, newVar);
		});
		localVars.forEach((varDecl, litExpr) -> {
			final VarDecl<?> newVar = Var(varDecl.getName() + "_" + counter++, varDecl.getType());
			if(FrontendMetadata.getMetadataValue(varDecl.getRef(), "cType").isPresent())
				FrontendMetadata.create(newVar.getRef(), "cType", CComplexType.getType(varDecl.getRef()));
			varLut.put(varDecl, newVar);
			ret.createVar(newVar, litExpr.orElse(null));
		});
		Map<XcfaLocation, XcfaLocation> locationLut = new LinkedHashMap<>();
		for (XcfaLocation location : new LinkedHashSet<>(locs)) {
			XcfaLocation copy = XcfaLocation.copyOf(location);
			ret.addLoc(copy);
			locationLut.put(location, copy);
		}
		ret.setFinalLoc(locationLut.get(finalLoc));
		ret.setInitLoc(locationLut.get(initLoc));
		if(errorLoc != null) ret.setErrorLoc(locationLut.get(errorLoc));
		for (XcfaEdge edge : edges) {
			ret.addEdge(XcfaEdge.of(locationLut.get(edge.getSource()), locationLut.get(edge.getTarget()), edge.getLabels().stream().map(label -> replacesVarsInStmt(label, v -> Optional.ofNullable(varLut.get(v)).map(varDecl -> cast(varDecl, v.getType()))).orElse(label)).collect(Collectors.toList())));
		}
		return ret;
	}

	public static Set<VarDecl<?>> getVars(XcfaLabel label) {
		if(label instanceof XcfaLabel.StmtXcfaLabel) return StmtUtils.getVars(label.getStmt());
		else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) return Set.of(((XcfaLabel.JoinThreadXcfaLabel) label).getKey());
		else if (label instanceof XcfaLabel.StartThreadXcfaLabel) return Sets.union(Set.of(((XcfaLabel.StartThreadXcfaLabel) label).getKey()), ExprUtils.getVars(((XcfaLabel.StartThreadXcfaLabel) label).getParam()));
		else if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
			Optional<Set<VarDecl<?>>> reduced = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().stream().map(ExprUtils::getVars).reduce(Sets::union);
			checkState(reduced.isPresent());
			return reduced.get();
		}
		else if (label instanceof XcfaLabel.StoreXcfaLabel) return Set.of(((XcfaLabel.StoreXcfaLabel<?>) label).getLocal(), ((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal());
		else if (label instanceof XcfaLabel.LoadXcfaLabel) return Set.of(((XcfaLabel.LoadXcfaLabel<?>) label).getLocal(), ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
		else if (label instanceof XcfaLabel.SequenceLabel) return ((XcfaLabel.SequenceLabel) label).getLabels().stream().map(Utils::getVars).reduce(Sets::union).orElseGet(Set::of);
		else if (label instanceof XcfaLabel.NondetLabel) return ((XcfaLabel.NondetLabel) label).getLabels().stream().map(Utils::getVars).reduce(Sets::union).orElseGet(Set::of);
		else if (label instanceof XcfaLabel.FenceXcfaLabel || label instanceof XcfaLabel.AtomicBeginXcfaLabel || label instanceof XcfaLabel.AtomicEndXcfaLabel) return Set.of();
		throw new UnsupportedOperationException("Unknown XcfaLabel type!");
	}

	public static Set<VarDecl<?>> getModifiedVars(XcfaLabel label) {
		if(label instanceof XcfaLabel.StmtXcfaLabel) {
			if(label.getStmt() instanceof HavocStmt) return Set.of(((HavocStmt<?>) label.getStmt()).getVarDecl());
			else if (label.getStmt() instanceof AssignStmt) return Set.of(((AssignStmt<?>) label.getStmt()).getVarDecl());
			else return Set.of();
		}
		else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) return Set.of();
		else if (label instanceof XcfaLabel.StartThreadXcfaLabel) return Set.of(((XcfaLabel.StartThreadXcfaLabel) label).getKey());
		else if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) { // Possibly modified vars included
			Optional<Set<VarDecl<?>>> reduced = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().stream().filter(expr -> expr instanceof RefExpr).map(ExprUtils::getVars).reduce(Sets::union);
			checkState(reduced.isPresent());
			return reduced.get();
		}
		else if (label instanceof XcfaLabel.StoreXcfaLabel) return Set.of(((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal());
		else if (label instanceof XcfaLabel.LoadXcfaLabel) return Set.of(((XcfaLabel.LoadXcfaLabel<?>) label).getLocal());
		else if (label instanceof XcfaLabel.SequenceLabel) return ((XcfaLabel.SequenceLabel) label).getLabels().stream().map(Utils::getModifiedVars).reduce(Sets::union).orElseGet(Set::of);
		else if (label instanceof XcfaLabel.NondetLabel) return ((XcfaLabel.NondetLabel) label).getLabels().stream().map(Utils::getModifiedVars).reduce(Sets::union).orElseGet(Set::of);
		else if (label instanceof XcfaLabel.FenceXcfaLabel || label instanceof XcfaLabel.AtomicBeginXcfaLabel || label instanceof XcfaLabel.AtomicEndXcfaLabel) return Set.of();
		throw new UnsupportedOperationException("Unknown XcfaLabel type!");
	}

	public static Set<VarDecl<?>> getNonModifiedVars(XcfaLabel label) {
		if(label instanceof XcfaLabel.StmtXcfaLabel) {
			if(label.getStmt() instanceof HavocStmt) return Set.of();
			else if (label.getStmt() instanceof AssignStmt) return ExprUtils.getVars(((AssignStmt<?>) label.getStmt()).getExpr());
			else return StmtUtils.getVars(label.getStmt());
		}
		else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) return Set.of(((XcfaLabel.JoinThreadXcfaLabel) label).getKey());
		else if (label instanceof XcfaLabel.StartThreadXcfaLabel) return Set.of();
		else if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) { // Possibly modified vars included
			Optional<Set<VarDecl<?>>> reduced = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().stream().map(ExprUtils::getVars).reduce(Sets::union);
			checkState(reduced.isPresent());
			return reduced.get();
		}
		else if (label instanceof XcfaLabel.StoreXcfaLabel) return Set.of(((XcfaLabel.StoreXcfaLabel<?>) label).getLocal());
		else if (label instanceof XcfaLabel.LoadXcfaLabel) return Set.of(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal());
		else if (label instanceof XcfaLabel.SequenceLabel) return ((XcfaLabel.SequenceLabel) label).getLabels().stream().map(Utils::getNonModifiedVars).reduce(Sets::union).orElseGet(Set::of);
		else if (label instanceof XcfaLabel.NondetLabel) return ((XcfaLabel.NondetLabel) label).getLabels().stream().map(Utils::getNonModifiedVars).reduce(Sets::union).orElseGet(Set::of);
		else if (label instanceof XcfaLabel.FenceXcfaLabel || label instanceof XcfaLabel.AtomicBeginXcfaLabel || label instanceof XcfaLabel.AtomicEndXcfaLabel) return Set.of();
		throw new UnsupportedOperationException("Unknown XcfaLabel type!");
	}
}
