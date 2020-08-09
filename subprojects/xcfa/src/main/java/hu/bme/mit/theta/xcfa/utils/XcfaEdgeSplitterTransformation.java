package hu.bme.mit.theta.xcfa.utils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
	
	private XcfaEdgeSplitterTransformation() {}
	
	public static XCFA transform(XCFA original) {
		return new XcfaEdgeSplitterTransformation()._transform(original);
	}
	
	// reuses variables and stmts
	private XCFA _transform(XCFA original) {
		XCFA.Builder builder = XCFA.builder();
		Map<Procedure, Procedure> origToNewProcedure = new HashMap<>();
		for (Process origPs: original.getProcesses()) {
			Process.Builder builderPs = XCFA.Process.builder(); 
			builderPs.setName(origPs.getName());
			for (Procedure origPc : origPs.getProcedures()) {
				Procedure.Builder builderPc = Procedure.builder();
				builderPc.setName(origPc.getName());
				var locMap = addLocations(builderPc, origPc);
				for (var origEdge : origPc.getEdges()) {
					addEdge(locMap, builderPc, origEdge);
				}
				for (var origParam : origPc.getParams()) {
					builderPc.createParam(origParam);
				}
				for (var origVar : origPc.getLocalVars()) {
					builderPc.createVar(origVar);
				}
				builderPc.setRtype(origPc.getRtype());
				builderPc.setResult(origPc.getResult());
				var pc = builderPc.build();
				builderPs.addProcedure(pc);
				origToNewProcedure.put(origPc, pc);
				if (origPs.getMainProcedure() == origPc) {
					builderPs.setMainProcedure(pc);
				}
			}
			for (var origVar : origPs.getThreadLocalVars()) {
				builderPs.createVar(origVar);
			}
			var ps = builderPs.build();
			builder.addProcess(ps);
			if (original.getMainProcess() == origPs) {
				builder.setMainProcess(ps);
			}
		}
		for (var origVar : original.getGlobalVars()) {
			builder.createVar(origVar);
		}
		for (var q : postBuildData) {
			var pc = origToNewProcedure.get(q.oldPc);
			q.stmt.setProcedure(pc);
		}
		postBuildData.clear();
		return builder.build();
	}

	// TODO use JRE11 feature instead
	private static List<Stmt> listOf(Stmt stmt) {
		var x = new ArrayList<Stmt>();
		x.add(stmt);
		return x;
	}
	
	private Map<Location, Location> addLocations(Procedure.Builder builder, Procedure orig) {
		Map<Location, Location> locMap = new HashMap<>();
		for (var origLoc : orig.getLocs()) {
			Location loc = new Location(origLoc.getName(), origLoc.getDictionary());
			locMap.put(origLoc, loc);
			builder.addLoc(loc);
			
			if (orig.getInitLoc() == origLoc) {
				builder.setInitLoc(loc);
			} else if (orig.getErrorLoc() == origLoc) {
				builder.setErrorLoc(loc);
			} else if (orig.getFinalLoc() == origLoc) {
				builder.setFinalLoc(loc);
			}
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
			var cc = new CallStmt(((CallStmt) stmt).getResultVar(), null, ((CallStmt) stmt).getParams());
			postBuildData.add(new CallStmtWithOldProcedure(cc, ((CallStmt) stmt).getProcedure()));
			return cc;
		} else {
			return stmt;
		}
	}

	private void addEdge(Map<Location, Location> locMap, Procedure.Builder builder, Edge origEdge) {
		var source = locMap.get(origEdge.getSource());
		var target = locMap.get(origEdge.getTarget());
		var stmts = origEdge.getStmts();
		if (stmts.size() == 0) {
			builder.addEdge(new Edge(source, target, listOf(SkipStmt.getInstance())));
//		} else if (stmts.size() == 1) {
//			builder.addEdge(new Edge(source, target, stmts));
		} else {
			Location lastLoc = source;
			// all but last edge
			for (var i = 0; i < stmts.size()-1; i++) {
				var stmt = stmts.get(i);
				Location loc = new Location("_" + source.getName() + "_" + target.getName() + "_" + i, source.getDictionary());
				builder.addLoc(loc);
				builder.addEdge(new Edge(lastLoc, loc, listOf(copyStmt(stmt))));
				lastLoc = loc;
			}
			// last edge
			builder.addEdge(new Edge(lastLoc, target, listOf(copyStmt(stmts.get(stmts.size()-1)))));
		}
	}
}