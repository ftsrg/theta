package hu.bme.mit.theta.xcfa.utils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

/**
 * Splits multiple-stmt edges
 * @author laszlo.radnai
 *
 */
public final class XcfaEdgeSplitterTransformation {
	
	private final Map<Procedure, Procedure> origToNewProcedure = new HashMap<>();
	private final XCFA original;

	private XcfaEdgeSplitterTransformation(XCFA xcfa) {
		original = xcfa;
	}
	
	public static XCFA transform(XCFA original) {
		return new XcfaEdgeSplitterTransformation(original)._transform();
	}
	
	// reuses variables and stmts
	private XCFA _transform() {
		XCFA.Builder builder = XCFA.builder();
		for (Process origPs: original.getProcesses()) {
			var ps = transformProcess(origPs);
			builder.addProcess(ps);
			if (original.getMainProcess() == origPs) {
				builder.setMainProcess(ps);
			}
		}
		for (var origVar : original.getVars()) {
			builder.createVar(origVar);
		}
		for (var q : postBuildData) {
			var pc = origToNewProcedure.get(q.oldPc);
			q.stmt.setProcedure(pc);
		}
		postBuildData.clear();
		return builder.build();
	}
	
	private Process transformProcess(Process origPs) {
		Process.Builder builderPs = XCFA.Process.builder(); 
		builderPs.setName(origPs.getName());
		for (Procedure origPc : origPs.getProcedures()) {
			var pc = transformProcedure(origPc);
			builderPs.addProcedure(pc);
			origToNewProcedure.put(origPc, pc);
			if (origPs.getMainProcedure() == origPc) {
				builderPs.setMainProcedure(pc);
			}
		}
		for (var origVar : origPs.getVars()) {
			builderPs.createVar(origVar);
		}
		return builderPs.build();
		
	}
	
	private Procedure transformProcedure(Procedure origPc) {
		Procedure.Builder builderPc = Procedure.builder();
		builderPc.setName(origPc.getName());
		var locMap = addLocations(builderPc, origPc);
		for (var origEdge : origPc.getEdges()) {
			transformEdge(locMap, builderPc, origEdge);
		}
		for (var origParam : origPc.getParams()) {
			builderPc.createParam(origParam);
		}
		for (var origVar : origPc.getVars()) {
			builderPc.createVar(origVar);
		}
		builderPc.setRtype(origPc.getRtype());
		builderPc.setResult(origPc.getResult());
		return builderPc.build();
	}
	
	private Location transformLocation(Procedure.Builder builder, Location origLoc, Procedure orig) {
		Location loc = new Location(origLoc.getName(), origLoc.getDictionary());
		builder.addLoc(loc);
		
		if (orig.getInitLoc() == origLoc) {
			builder.setInitLoc(loc);
		} else if (orig.getErrorLoc() == origLoc) {
			builder.setErrorLoc(loc);
		} else if (orig.getFinalLoc() == origLoc) {
			builder.setFinalLoc(loc);
		}
		return loc;
	}
	
	private Map<Location, Location> addLocations(Procedure.Builder builder, Procedure orig) {
		Map<Location, Location> locMap = new HashMap<>();
		for (var origLoc : orig.getLocs()) {
			locMap.put(origLoc, transformLocation(builder, origLoc, orig));
		}
		return locMap;
	}
	
	private static class CallStmtWithOldProcedure {
		private final CallStmt stmt;
		private final Procedure oldPc;
		public CallStmtWithOldProcedure(CallStmt stmt, Procedure oldPc) {
			this.stmt = stmt;
			this.oldPc = oldPc;
		}
	}
	
	private final List<CallStmtWithOldProcedure> postBuildData = new ArrayList<>();
	
	/**
	 * Ensures no references of the old XCFA remains in a Stmt.
	 * Might reuse stmt.
	 * 
	 * Variables, stmts are not a problem.
	 * CallStmts must be copied, however.
	 * @return
	 */
	private Stmt copyStmt(Stmt stmt) {
		if (stmt instanceof CallStmt) {
			// We cannot yet fill the *new* procedure, because it might not have been built yet.
			var cc = new CallStmt(((CallStmt) stmt).getVar(), null, ((CallStmt) stmt).getParams());
			postBuildData.add(new CallStmtWithOldProcedure(cc, ((CallStmt) stmt).getProcedure()));
			return cc;
		} else {
			return stmt;
		}
	}
	
	private void splitEdge(Procedure.Builder builder, Location source, Location target, List<Stmt> copiedStmts) {
		if (copiedStmts.size() == 0) {
			builder.addEdge(new Edge(source, target, List.of(SkipStmt.getInstance())));
		} else {
			Location lastLoc = source;
			// all but last edge
			for (var i = 0; i < copiedStmts.size()-1; i++) {
				var stmt = copiedStmts.get(i);
				Location loc = new Location("_" + source.getName() + "_" + target.getName() + "_" + i, source.getDictionary());
				builder.addLoc(loc);
				builder.addEdge(new Edge(lastLoc, loc, List.of(stmt)));
				lastLoc = loc;
			}
			// last edge
			builder.addEdge(new Edge(lastLoc, target, List.of(copiedStmts.get(copiedStmts.size()-1))));
		}
	}

	private void transformEdge(Map<Location, Location> locMap, Procedure.Builder builder, Edge origEdge) {
		var source = locMap.get(origEdge.getSource());
		var target = locMap.get(origEdge.getTarget());
		var stmts = origEdge.getStmts();
		splitEdge(builder, source, target, stmts.stream().map(s -> copyStmt(s)).collect(Collectors.toList()));
	}
}