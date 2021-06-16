package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.CIntTypeUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import hu.bme.mit.theta.xcfa.transformation.c.types.NamedType;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.AssignStmt.of;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class FunctionInlining extends ProcessPass {
	private int counter = 0;
	private final List<String> nopFuncs = List.of("reach_error", "abort");
	private final Set<Stmt> alreadyHandled = new LinkedHashSet<>();

	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		ProcedurePass.postInlining = true;
		alreadyHandled.clear();
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

	private XcfaProcedure inlineProcedure(XcfaProcess.Builder builder, XcfaProcess.Builder newBuilder, XcfaProcedure procedure) {
		XcfaProcedure.Builder procBuilder = XcfaProcedure.builder();
		for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : procedure.getParams().entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			XcfaProcedure.Direction direction = entry.getValue();
			procBuilder.createParam(direction, varDecl);
		}
		procBuilder.setName(procedure.getName());
		for (VarDecl<?> localVar : procedure.getLocalVars()) {
			procBuilder.createVar(localVar, null);
		}
		for (XcfaLocation loc : procedure.getLocs()) {
			procBuilder.addLoc(loc);
			loc.setEndLoc(false);
		}
		for (XcfaEdge edge : procedure.getEdges()) {
			procBuilder.addEdge(edge);
		}
		procBuilder.setInitLoc(procedure.getInitLoc());
		procBuilder.setFinalLoc(procedure.getFinalLoc());
		procBuilder.setFinalLoc(procedure.getFinalLoc());
		Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints = new LinkedHashMap<>();


		while(handleCallStmts(builder, procedure, procBuilder, splittingPoints)) {
			splitAndInlineEdges(builder, procBuilder, splittingPoints);
			splittingPoints.clear();
		}

		// TODO function calls
		truncateAssignments(builder, procBuilder);

		XcfaProcedure built = procBuilder.build();
		newBuilder.addProcedure(built);
		return built;
	}

	/**
	 * In assignments we need to convert the C type of the right hand expression to the C type of the left one.
	 * In the case, where the left type is smaller in maximum size than the right one, we'll truncate the value.
	 * We need to add a modulo to the right expression in this case to truncate.
	 */
	private void truncateAssignments(XcfaProcess.Builder builder, XcfaProcedure.Builder procBuilder) {
		List<XcfaEdge> edgesCopy = new ArrayList<>(procBuilder.getEdges());
		for (XcfaEdge edge : edgesCopy) {
			boolean atLeastOneAssignmentTruncated = false;
			List<Stmt> newStmts = new ArrayList<>(edge.getStmts());
			for (Stmt stmt : edge.getStmts()) {
				if (stmt instanceof AssignStmt) {
					AssignStmt<?> assignStmt = (AssignStmt<?>) stmt;
					NamedType leftType = CIntTypeUtils.getcTypeMetadata(assignStmt.getVarDecl().getRef());
					checkNotNull(leftType);
					Expr<IntType> expr = cast(assignStmt.getExpr(), Int());

					Expr<IntType> truncatedExpr = CIntTypeUtils.truncateToType(leftType, expr);
					if (!expr.equals(truncatedExpr)) {
						atLeastOneAssignmentTruncated = true;
						newStmts.remove(stmt);
						AssignStmt<IntType> newStmt = AssignStmt.of(cast(assignStmt.getVarDecl(), Int()) , truncatedExpr);
						newStmts.add(newStmt);
					}
				}
			}
			if (atLeastOneAssignmentTruncated) {
				XcfaEdge newEdge = new XcfaEdge(edge.getSource(), edge.getTarget(), newStmts);
				XcfaMetadata.lookupMetadata(edge).forEach((s, o) -> {
					XcfaMetadata.create(newEdge, s, o);
				});
				procBuilder.removeEdge(edge);
				procBuilder.addEdge(newEdge);
			}
		}


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
					NamedType funcParamType = CIntTypeUtils.getcTypeMetadata(varDecl.getRef());
					checkNotNull(funcParamType);
					Expr<IntType> param = cast(xcfaCallStmt.getParams().get(paramCnt), Int());
					Expr<IntType> truncatedParam = CIntTypeUtils.truncateToType(funcParamType, param);

					AssignStmt<IntType> assignStmt = Assign(cast(varDecl, Int()), truncatedParam);
					initStmts.add(assignStmt);
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
