package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaStmtVarReplacer;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;

public class BMCTraditional {
	private static final int MAX_K = 102400;

	public Tuple2<Boolean, List<XcfaEdge>> getCex(XcfaProcedure procedure) {
		if(procedure.getErrorLoc() == null) return Tuple2.of(true, List.of());

		Solver solver = Z3SolverFactory.getInstance().createSolver();
		Map<XcfaLocation, Tuple3<Solver, List<XcfaEdge>, Map<VarDecl<?>, ConstDecl<?>>>> currentDepth = new LinkedHashMap<>();
		currentDepth.put(procedure.getInitLoc(), Tuple3.of(solver, new ArrayList<>(), new LinkedHashMap<>()));

		for(int i = 0; i < MAX_K; i++) {
			if(currentDepth.size() == 0) return Tuple2.of(true, List.of());

			for (Map.Entry<XcfaLocation, Tuple3<Solver, List<XcfaEdge>, Map<VarDecl<?>, ConstDecl<?>>>> entry : new LinkedHashSet<>(currentDepth.entrySet())) {
				XcfaLocation currentLoc = entry.getKey();
				Tuple3<Solver, List<XcfaEdge>, Map<VarDecl<?>, ConstDecl<?>>> currentValue = entry.getValue();
				currentDepth.remove(currentLoc);

				List<Tuple3<Solver, List<XcfaEdge>, Map<VarDecl<?>, ConstDecl<?>>>> nextValues = new ArrayList<>();
				nextValues.add(currentValue);
				for (int i1 = 1; i1 < currentLoc.getOutgoingEdges().size(); i1++) {
					Solver newSolver = Z3SolverFactory.getInstance().createSolver();
					newSolver.add(currentValue.get1().getAssertions());
					nextValues.add(Tuple3.of(newSolver, new ArrayList<>(currentValue.get2()), new LinkedHashMap<>(currentValue.get3())));
				}

				for (int i1 = 0; i1 < currentLoc.getOutgoingEdges().size(); i1++) {
					XcfaEdge outgoingEdge = currentLoc.getOutgoingEdges().get(i1);
					Map<VarDecl<?>, ConstDecl<?>> varToLastConstMap = nextValues.get(i1).get3();
					Solver newSolver = nextValues.get(i1).get1();
					for (Stmt stmt : outgoingEdge.getStmts()) {
						for (VarDecl<?> var : StmtUtils.getVars(stmt)) {
							if(!varToLastConstMap.containsKey(var)) varToLastConstMap.put(var, Const(var.getName(), var.getType()));
						}
						if (stmt instanceof HavocStmt) {
							VarDecl<?> var = ((HavocStmt<?>) stmt).getVarDecl();
							varToLastConstMap.put(var, Const(var.getName(), var.getType()));
						} else if (stmt instanceof AssumeStmt) {
							Expr<BoolType> expr = XcfaStmtVarReplacer.replaceVars(((AssumeStmt) stmt).getCond(), varToLastConstMap);
							newSolver.add(expr);
						} else if (stmt instanceof AssignStmt) {
							VarDecl<?> var = ((AssignStmt<?>) stmt).getVarDecl();
							ConstDecl<?> cnst = Const(var.getName(), var.getType());
							Expr<BoolType> expr = Eq(cnst.getRef(), XcfaStmtVarReplacer.replaceVars(((AssignStmt<?>) stmt).getExpr(), varToLastConstMap));
							newSolver.add(expr);
							varToLastConstMap.put(var, cnst);
						} else throw new UnsupportedOperationException("Not yet implemented!");
					}
					newSolver.check();
					if(newSolver.getStatus().isSat()) {
						nextValues.get(i1).get2().add(outgoingEdge);
						if(outgoingEdge.getTarget().isErrorLoc()) return Tuple2.of(false, nextValues.get(i1).get2());
						currentDepth.put(outgoingEdge.getTarget(), nextValues.get(i1));
					}
				}
			}
			System.out.println("BMC has not found a violation in iteration " + i);
		}

		return null;
	}
}
