package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVarReplacer;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;

public class Utils {

	public static List<XcfaEdge> collectPaths(XcfaLocation start, XcfaLocation end) {
		return collectPaths(start, new SetStack<>(), end, new LinkedHashMap<>(), Z3SolverFactory.getInstance().createSolver());
	}

	private static List<XcfaEdge> collectPaths(XcfaLocation current, SetStack<XcfaEdge> path, XcfaLocation end, Map<VarDecl<?>, ConstDecl<?>> varToLastConstMap, Solver solver) {
		if(current == end) {
			return path.getList();
		}
		List<XcfaEdge> outgoingEdges = current.getOutgoingEdges();
		Map<VarDecl<?>, ConstDecl<?>> saved = new LinkedHashMap<>(varToLastConstMap);
		for (XcfaEdge outgoingEdge : outgoingEdges) {
			if(!path.contains(outgoingEdge)) {
				path.push(outgoingEdge);
				solver.push();
				for (Stmt stmt : outgoingEdge.getLabels()) {
					for (VarDecl<?> var : StmtUtils.getVars(stmt)) {
						if(!varToLastConstMap.containsKey(var)) varToLastConstMap.put(var, Const(var.getName(), var.getType()));
					}
					if (stmt instanceof HavocStmt) {
						VarDecl<?> var = ((HavocStmt<?>) stmt).getVarDecl();
						varToLastConstMap.put(var, Const(var.getName(), var.getType()));
					} else if (stmt instanceof AssumeStmt) {
						Expr<BoolType> expr = XcfaLabelVarReplacer.replaceVars(((AssumeStmt) stmt).getCond(), varToLastConstMap);
						solver.add(expr);
					} else if (stmt instanceof AssignStmt) {
						VarDecl<?> var = ((AssignStmt<?>) stmt).getVarDecl();
						ConstDecl<?> cnst = Const(var.getName(), var.getType());
						Expr<BoolType> expr = Eq(cnst.getRef(), XcfaLabelVarReplacer.replaceVars(((AssignStmt<?>) stmt).getExpr(), varToLastConstMap));
						solver.add(expr);
						varToLastConstMap.put(var, cnst);
					} else throw new UnsupportedOperationException("Not yet implemented!");
				}
				solver.check();
				if(solver.getStatus().isSat()) {
					List<XcfaEdge> ret = collectPaths(outgoingEdge.getTarget(), path, end, varToLastConstMap, solver);
					if (ret != null) return ret;
				}
				solver.pop();
				path.pop();
				varToLastConstMap = saved;
			}
		}
		return null;
	}

	private static void createConst(Map<VarDecl<?>, Stack<ConstDecl<?>>> varToLastConstMap, VarDecl<?> var) {
		varToLastConstMap.putIfAbsent(var, new Stack<>());
		varToLastConstMap.get(var).push(Const(var.getName(), var.getType()));

	}


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

	private static XcfaProcedure.Builder getBuilder(String name, Type retType, List<XcfaLocation> locs, XcfaLocation finalLoc, XcfaLocation initLoc, XcfaLocation errorLoc, List<XcfaEdge> edges, Map<VarDecl<?>, XcfaProcedure.Direction> params, Map<VarDecl<?>, Optional<LitExpr<?>>> localVars) {
		XcfaProcedure.Builder ret = XcfaProcedure.builder();
		ret.setName(name);
		ret.setRetType(retType);
		params.forEach((varDecl, direction) -> ret.createParam(direction, varDecl));
		localVars.forEach((varDecl, litExpr) -> ret.createVar(varDecl, litExpr.orElse(null)));
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
			ret.addEdge(new XcfaEdge(locationLut.get(edge.getSource()), locationLut.get(edge.getTarget()), edge.getLabels()));
		}
		return ret;
	}
}
