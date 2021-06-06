package hu.bme.mit.theta.xcfa.passes;

import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.AssignmentChainRemoval;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToFinalLocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToHavocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeSkipPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.HavocAssignments;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.PthreadCallsToThreadStmts;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;
import hu.bme.mit.theta.xcfa.passes.processpass.FunctionInlining;
import hu.bme.mit.theta.xcfa.passes.processpass.ProcessPass;
import hu.bme.mit.theta.xcfa.passes.xcfapass.RemoveUnusedGlobals;
import hu.bme.mit.theta.xcfa.passes.xcfapass.XcfaPass;

import java.util.ArrayList;
import java.util.List;

public class XcfaPassManager {
	private static final List<ProcedurePass> procedurePasses = new ArrayList<>();
	private static final List<ProcessPass> processPasses = new ArrayList<>();
	private static final List<XcfaPass> xcfaPasses = new ArrayList<>();

	static {
		procedurePasses.addAll(List.of(
				new PthreadCallsToThreadStmts(),
				new CallsToFinalLocs(),
				new CallsToHavocs(),
				new HavocAssignments(),
				new UnusedVarRemovalPass(),
				new AssignmentChainRemoval(),
				new EmptyEdgeRemovalPass(),
				new EmptyEdgeSkipPass()));
		processPasses.addAll(List.of(
				new FunctionInlining()));
		xcfaPasses.addAll((List.of(
				new RemoveUnusedGlobals())));
	}

	public static void addProcedurePass(ProcedurePass pass) {
		procedurePasses.add(pass);
	}
	public static void addProcessPass(ProcessPass pass) {
		processPasses.add(pass);
	}
	public static void addXcfaPass(XcfaPass pass) {
		xcfaPasses.add(pass);
	}

	public static XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (ProcedurePass procedurePass : procedurePasses) {
			if(!procedurePass.isPostInlining() || ProcedurePass.postInlining) builder = procedurePass.run(builder);
		}
		return builder;
	}

	public static XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		for (ProcessPass processPass : processPasses) {
			builder = processPass.run(builder);
		}
		return builder;
	}

	public static XCFA.Builder run(XCFA.Builder builder) {
		for (XcfaPass xcfaPass : xcfaPasses) {
			builder = xcfaPass.run(builder);
		}
		return builder;
	}
}
