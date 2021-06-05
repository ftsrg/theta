package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToFinalLocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToHavocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.HavocAssignments;
import hu.bme.mit.theta.xcfa.passes.procedurepass.PthreadCallsToThreadStmts;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class FunctionInlining implements ProcessPass{
	private int counter = 0;
	private final List<String> nopFuncs = List.of("reach_error", "abort");

	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		XcfaProcess.Builder newBuilder = XcfaProcess.builder();
		newBuilder.setName(builder.getName());
		newBuilder.getThreadLocalVars().putAll(builder.getThreadLocalVars());
		for (VarDecl<?> param : builder.getParams()) {
			newBuilder.createParam(param);
		}
		XcfaProcedure mainProcedure = builder.getMainProcedure();
		XcfaProcedure newMainProc = inlineProcedure(builder, newBuilder, mainProcedure);
		newBuilder.setMainProcedure(newMainProc);

		boolean foundOne = true;
		while(foundOne) {
			foundOne = false;
			for (XcfaProcedure procedure : new ArrayList<>(newBuilder.getProcedures())) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (Stmt stmt : edge.getStmts()) {
						if(stmt instanceof StartThreadStmt) {
							String threadName = ((StartThreadStmt) stmt).getThreadName();
							Optional<XcfaProcedure> func = newBuilder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(threadName)).findAny();
							if(func.isEmpty()) {
								Optional<XcfaProcedure> oldProc = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(threadName)).findAny();
								if(oldProc.isPresent()) {
									foundOne = true;
									inlineProcedure(builder, newBuilder, oldProc.get());
								}
							}
						}
					}
				}
			}
		}

		return newBuilder;

	}

	private XcfaProcedure inlineProcedure(XcfaProcess.Builder builder, XcfaProcess.Builder newBuilder, XcfaProcedure mainProcedure) {
		XcfaProcedure.Builder mainProcBuilder = XcfaProcedure.builder();
		for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : mainProcedure.getParams().entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			XcfaProcedure.Direction direction = entry.getValue();
			mainProcBuilder.createParam(direction, varDecl);
		}
		mainProcBuilder.setName(mainProcedure.getName());
		for (VarDecl<?> localVar : mainProcedure.getLocalVars()) {
			mainProcBuilder.createVar(localVar, null);
		}
		for (XcfaLocation loc : mainProcedure.getLocs()) {
			mainProcBuilder.addLoc(loc);
			loc.setEndLoc(false);
		}
		for (XcfaEdge edge : mainProcedure.getEdges()) {
			mainProcBuilder.addEdge(edge);
		}
		mainProcBuilder.setInitLoc(mainProcedure.getInitLoc());
		mainProcBuilder.setFinalLoc(mainProcedure.getFinalLoc());
		mainProcBuilder.setFinalLoc(mainProcedure.getFinalLoc());
		Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints = new LinkedHashMap<>();


		while(handleCallStmts(builder, mainProcedure, mainProcBuilder, splittingPoints)) {
			splitAndInlineEdges(builder, mainProcBuilder, splittingPoints);
			splittingPoints.clear();
		}


		mainProcBuilder = new PthreadCallsToThreadStmts().run(mainProcBuilder);
		mainProcBuilder = new CallsToFinalLocs().run(mainProcBuilder);
		mainProcBuilder = new CallsToHavocs().run(mainProcBuilder);
		mainProcBuilder = new HavocAssignments().run(mainProcBuilder);
		mainProcBuilder = new EmptyEdgeRemovalPass().run(mainProcBuilder);
		mainProcBuilder = new UnusedVarRemovalPass().run(mainProcBuilder);
		mainProcBuilder = new EmptyEdgeRemovalPass().run(mainProcBuilder);
		XcfaProcedure built = mainProcBuilder.build();
		newBuilder.addProcedure(built);
		return built;
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
				XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					XcfaMetadata.create(loc1, s, o);
				});
				procBuilder.addLoc(loc1);
				XcfaEdge edge = new XcfaEdge(start, loc1, sublist(xcfaEdge.getStmts(), 0, i));
				procBuilder.addEdge(edge);
				XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					XcfaMetadata.create(edge, s, o);
				});
				start = loc1;
			}
			if(i < xcfaEdge.getStmts().size() - 1) {
				XcfaLocation loc1 = new XcfaLocation("inline" + counter++, Map.of());
				XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					XcfaMetadata.create(loc1, s, o);
				});
				procBuilder.addLoc(loc1);
				XcfaEdge edge = new XcfaEdge(loc1, end, sublist(xcfaEdge.getStmts(), i + 1, xcfaEdge.getStmts().size()));
				procBuilder.addEdge(edge);
				XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					XcfaMetadata.create(edge, s, o);
				});
				end = loc1;
			}
			Optional<XcfaProcedure> procedureOpt = oldBuilder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(xcfaCallStmt.getProcedure())).findAny();
			checkState(procedureOpt.isPresent());
			XcfaProcedure procedure = new XcfaProcedure(procedureOpt.get());
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
			XcfaEdge xcfaEdge1 = new XcfaEdge(start, procedure.getInitLoc(), initStmts);
			XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
				XcfaMetadata.create(xcfaEdge1, s, o);
			});
			XcfaEdge xcfaEdge2 = new XcfaEdge(procedure.getFinalLoc(), end, retStmts);
			XcfaMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
				XcfaMetadata.create(xcfaEdge2, s, o);
			});
			procBuilder.addEdge(xcfaEdge1);
			procBuilder.addEdge(xcfaEdge2);
		});
	}

	private List<Stmt> sublist(List<Stmt> stmts, int from, int to) {
		List<Stmt> ret = new ArrayList<>();
		for (int i = 0; i < stmts.size(); i++) {
			if(i >= from && i < to) ret.add(stmts.get(i));
		}
		return ret;
	}


	Set<Stmt> alreadyHandled = new LinkedHashSet<>();
	private boolean handleCallStmts(XcfaProcess.Builder builder, XcfaProcedure mainProcedure, XcfaProcedure.Builder mainProcBuilder, Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints) {
		boolean anyMatch = false;
		for (XcfaEdge edge : mainProcBuilder.getEdges()) {
			boolean stillExists = true;
			while(stillExists) {
				Optional<Stmt> callStmtOpt = edge.getStmts().stream().filter(stmt ->
						stmt instanceof XcfaCallStmt &&
						!alreadyHandled.contains(stmt) &&
						!nopFuncs.contains(((XcfaCallStmt)stmt).getProcedure()) &&
						shouldInlineCall(builder, (XcfaCallStmt) stmt)).findAny();
				if(callStmtOpt.isPresent() ) {
					alreadyHandled.add(callStmtOpt.get());
					anyMatch = true;
					Optional<XcfaProcedure> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(((XcfaCallStmt) callStmtOpt.get()).getProcedure())).findAny();
					if (procedure.isPresent()) {
						splittingPoints.putIfAbsent(edge, new ArrayList<>());
						splittingPoints.get(edge).add((XcfaCallStmt) callStmtOpt.get());
					}
				} else {
					stillExists = false;
				}
			}
		}
		return anyMatch;
	}

	private boolean shouldInlineCall(XcfaProcess.Builder builder, XcfaCallStmt callStmt) {
		Optional<XcfaProcedure> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callStmt.getProcedure())).findAny();
		if(procedure.isPresent()) {
			Optional<Object> sourceStatement = XcfaMetadata.getMetadataValue(procedure.get(), "sourceStatement");
			if(sourceStatement.isPresent()) {
				Optional<Object> shouldInline = XcfaMetadata.getMetadataValue(sourceStatement.get(), "shouldInline");
				return shouldInline.isEmpty() || !(shouldInline.get() instanceof Boolean) || (Boolean) shouldInline.get();
			}
		}
		return true;
	}
}
