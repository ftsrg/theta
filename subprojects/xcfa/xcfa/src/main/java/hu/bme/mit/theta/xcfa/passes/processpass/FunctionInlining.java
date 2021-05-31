package hu.bme.mit.theta.xcfa.passes.processpass;

import com.google.common.base.Predicates;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToErrorLocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class FunctionInlining implements ProcessPass{
	private int counter = 0;
	private List<String> errorFuncs = List.of("abort");

	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		XcfaProcess.Builder newBuilder = XcfaProcess.builder();
		newBuilder.setName(builder.getName());
		newBuilder.getThreadLocalVars().putAll(builder.getThreadLocalVars());
		for (VarDecl<?> param : builder.getParams()) {
			newBuilder.createParam(param);
		}
		XcfaProcedure mainProcedure = builder.getMainProcedure();
		XcfaProcedure.Builder mainProcBuilder = XcfaProcedure.builder();
		mainProcedure.getParams().forEach((varDecl, direction) -> mainProcBuilder.createParam(direction, varDecl));
		mainProcBuilder.setName(mainProcedure.getName());
		for (VarDecl<?> localVar : mainProcedure.getLocalVars()) {
			mainProcBuilder.createVar(localVar, null);
		}
		for (XcfaLocation loc : mainProcedure.getLocs()) {
			mainProcBuilder.addLoc(loc);
		}
		for (XcfaEdge edge : mainProcedure.getEdges()) {
			mainProcBuilder.addEdge(edge);
		}
		mainProcBuilder.setInitLoc(mainProcedure.getInitLoc());
		mainProcBuilder.setFinalLoc(mainProcedure.getFinalLoc());
		mainProcBuilder.setFinalLoc(mainProcedure.getFinalLoc());
		Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints = new LinkedHashMap<>();
		Map<XcfaEdge, List<XcfaCallStmt>> havocStmts = new LinkedHashMap<>();


		while(handleCallStmts(builder, mainProcedure, mainProcBuilder, splittingPoints, havocStmts)) {
			havocEdges(builder, mainProcBuilder, havocStmts);
			splitAndInlineEdges(builder, mainProcBuilder, splittingPoints);
			splittingPoints.clear();
			havocStmts.clear();
		}
		XcfaProcedure.Builder funcBuilder = new CallsToErrorLocs().run(mainProcBuilder);
		funcBuilder = new UnusedVarRemovalPass().run(funcBuilder);
		funcBuilder = new EmptyEdgeRemovalPass().run(funcBuilder);
		XcfaProcedure built = funcBuilder.build();
		newBuilder.addProcedure(built);
		newBuilder.setMainProcedure(built);
		return newBuilder;

	}

	private void havocEdges(XcfaProcess.Builder oldBuilder, XcfaProcedure.Builder procBuilder, Map<XcfaEdge, List<XcfaCallStmt>> havocStmts) {
		havocStmts.forEach((xcfaEdge, xcfaCallStmts) -> {
			for (XcfaCallStmt xcfaCallStmt : xcfaCallStmts) {
				procBuilder.removeEdge(xcfaEdge);
				List<Stmt> havocs = new ArrayList<>();
//				for (Expr<?> expr : xcfaCallStmt.getParams()) { // TODO: here all OUT params should be havoced
				Expr<?> expr = xcfaCallStmt.getParams().get(0);
					checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl);
					VarDecl<?> var = (VarDecl<?>) ((RefExpr<?>) expr).getDecl();
					havocs.add(Havoc(var));
//				}
				List<Stmt> newStmts = new ArrayList<>();
				for (Stmt stmt : xcfaEdge.getStmts()) {
					if(stmt == xcfaCallStmt) newStmts.addAll(havocs);
					else newStmts.add(stmt);
				}

				procBuilder.addEdge(new XcfaEdge(xcfaEdge.getSource(), xcfaEdge.getTarget(), newStmts));
			}
		});
	}

	private void splitAndInlineEdges(XcfaProcess.Builder oldBuilder, XcfaProcedure.Builder procBuilder, Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints) {
		splittingPoints.forEach((xcfaEdge, xcfaCallStmts) -> {
			procBuilder.removeEdge(xcfaEdge);
			XcfaCallStmt xcfaCallStmt = xcfaCallStmts.get(0);
			int i = xcfaEdge.getStmts().indexOf(xcfaCallStmt);
			XcfaLocation start = xcfaEdge.getSource();
			XcfaLocation end = xcfaEdge.getTarget();
			if(i > 0) {
				XcfaLocation loc1 = new XcfaLocation("inline" + counter++, Map.of());
				procBuilder.addLoc(loc1);
				procBuilder.addEdge(new XcfaEdge(start, loc1, sublist(xcfaEdge.getStmts(), 0, i)));
				start = loc1;
			}
			if(i < xcfaEdge.getStmts().size() - 1) {
				XcfaLocation loc1 = new XcfaLocation("inline" + counter++, Map.of());
				procBuilder.addLoc(loc1);
				procBuilder.addEdge(new XcfaEdge(loc1, end, sublist(xcfaEdge.getStmts(), i + 1, xcfaEdge.getStmts().size())));
				end = loc1;
			}
			Optional<XcfaProcedure> procedureOpt = oldBuilder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(xcfaCallStmt.getProcedure())).findAny();
			checkState(procedureOpt.isPresent());
			XcfaProcedure procedure = procedureOpt.get();
			for (VarDecl<?> localVar : procedure.getLocalVars()) {
				procBuilder.createVar(localVar, null);
			}
			procedure.getParams().forEach((varDecl, direction) -> procBuilder.createVar(varDecl, null));
			procedure.getLocs().forEach(procBuilder::addLoc);
			procedure.getEdges().forEach(procBuilder::addEdge);

			int paramCnt = 0;
			List<Stmt> retStmts = new ArrayList<>();
			List<Stmt> initStmts = new ArrayList<>();
			for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : procedure.getParams().entrySet()) {
				VarDecl<?> varDecl = entry.getKey();
				XcfaProcedure.Direction direction = entry.getValue();
				if (direction != XcfaProcedure.Direction.OUT) {
					initStmts.add(Assign(cast(varDecl, varDecl.getType()), cast(xcfaCallStmt.getParams().get(paramCnt), varDecl.getType())));
				}
				if (direction != XcfaProcedure.Direction.IN) {
					Expr<?> expr = xcfaCallStmt.getParams().get(paramCnt);
					checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>);
					retStmts.add(Assign(cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), varDecl.getType()), cast(varDecl.getRef(), varDecl.getType())));
				}
				++paramCnt;
			}

			procBuilder.addEdge(new XcfaEdge(start, procedure.getInitLoc(), initStmts));
			procBuilder.addEdge(new XcfaEdge(procedure.getFinalLoc(), end, retStmts));
		});
	}

	private List<Stmt> sublist(List<Stmt> stmts, int from, int to) {
		List<Stmt> ret = new ArrayList<>();
		for (int i = 0; i < stmts.size(); i++) {
			if(i >= from && i < to) ret.add(stmts.get(i));
		}
		return ret;
	}


	private boolean handleCallStmts(XcfaProcess.Builder builder, XcfaProcedure mainProcedure, XcfaProcedure.Builder mainProcBuilder, Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints, Map<XcfaEdge, List<XcfaCallStmt>> havocStmts) {
		boolean anyMatch = false;
		Set<Stmt> alreadyHandled = new LinkedHashSet<>();
		for (XcfaEdge edge : mainProcBuilder.getEdges()) {
			boolean stillExists = true;
			while(stillExists) {
				Optional<Stmt> callStmtOpt = edge.getStmts().stream().filter(stmt -> stmt instanceof XcfaCallStmt && !alreadyHandled.contains(stmt) && !errorFuncs.contains(((XcfaCallStmt)stmt).getProcedure())).findAny();
				if(callStmtOpt.isPresent() ) {
					alreadyHandled.add(callStmtOpt.get());
					anyMatch = true;
					Optional<XcfaProcedure> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(((XcfaCallStmt) callStmtOpt.get()).getProcedure())).findAny();
					if (procedure.isPresent()) {
						splittingPoints.putIfAbsent(edge, new ArrayList<>());
						splittingPoints.get(edge).add((XcfaCallStmt) callStmtOpt.get());
					} else {
						havocStmts.putIfAbsent(edge, new ArrayList<>());
						havocStmts.get(edge).add((XcfaCallStmt) callStmtOpt.get());
					}
				} else {
					stillExists = false;
				}
			}
		}
		return anyMatch;
	}
}
