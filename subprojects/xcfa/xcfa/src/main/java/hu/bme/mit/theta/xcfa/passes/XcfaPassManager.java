package hu.bme.mit.theta.xcfa.passes;

import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.AddAtomicBeginEndsToFunctions;
import hu.bme.mit.theta.xcfa.passes.procedurepass.AddHavocRange;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToFinalLocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.CallsToHavocs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ConditionalFinalsToAssumes;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EliminateSelfLoops;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.FpFunctionsToExprs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.HavocPromotion;
import hu.bme.mit.theta.xcfa.passes.procedurepass.InitMemory;
import hu.bme.mit.theta.xcfa.passes.procedurepass.NoReadVarRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.PorPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.PthreadCallsToThreadStmts;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ReferenceToMemory;
import hu.bme.mit.theta.xcfa.passes.procedurepass.RemoveDeadEnds;
import hu.bme.mit.theta.xcfa.passes.procedurepass.SimpleLbePass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.SimplifyExprs;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.VerifierFunctionsToLabels;
import hu.bme.mit.theta.xcfa.passes.processpass.AnalyzeCallGraph;
import hu.bme.mit.theta.xcfa.passes.processpass.FunctionCallsToPushPops;
import hu.bme.mit.theta.xcfa.passes.processpass.FunctionInlining;
import hu.bme.mit.theta.xcfa.passes.processpass.ProcessPass;
import hu.bme.mit.theta.xcfa.passes.xcfapass.DemoteThreadLocalGlobals;
import hu.bme.mit.theta.xcfa.passes.xcfapass.RemoveUnusedGlobals;
import hu.bme.mit.theta.xcfa.passes.xcfapass.XcfaPass;

import java.util.ArrayList;
import java.util.List;

public class XcfaPassManager {
	private static final List<ProcedurePass> procedurePasses = new ArrayList<>();
	private static final List<ProcessPass> processPasses = new ArrayList<>();
	private static final List<XcfaPass> xcfaPasses = new ArrayList<>();

	private static final boolean bottomUp = true;

	static {
		procedurePasses.addAll(List.of(
				new EliminateSelfLoops(),
				new PthreadCallsToThreadStmts(),
				new VerifierFunctionsToLabels(),
				new AddAtomicBeginEndsToFunctions(),
				new ReferenceToMemory(),
				new InitMemory(),
				new FpFunctionsToExprs(),
				new SimplifyExprs(),
//				new SimplifyAssumptions(),
				new CallsToFinalLocs(),
				new CallsToHavocs(),
//				new HavocAssignments(),
				//new UnusedVarRemovalPass(),
				new EmptyEdgeRemovalPass(),
				new ConditionalFinalsToAssumes(),
				//new UnusedVarRemovalPass(),
				new AddHavocRange(),
				new RemoveDeadEnds(),
				//new UnusedVarRemovalPass(),
				new SimplifyExprs(),
				new EmptyEdgeRemovalPass(),
				new SimpleLbePass(),
				new PorPass(),
				new HavocPromotion(),
//				new AssignmentChainRemoval(),
				new NoReadVarRemovalPass(),
//				new GlobalVarsToStoreLoad(),
				new UnusedVarRemovalPass(),
				new EmptyEdgeRemovalPass(),
				new RemoveDeadEnds()
				));
		processPasses.addAll(List.of(
				new AnalyzeCallGraph(),
				new FunctionInlining(),
				new FunctionCallsToPushPops()));
		xcfaPasses.addAll((List.of(
				new RemoveUnusedGlobals(),
				new DemoteThreadLocalGlobals())));
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
	public static void clearProcedurePasses() {
		procedurePasses.clear();
	}
	public static void clearProcessPasses() {
		processPasses.clear();
	}
	public static void clearXCFAPasses() {
		xcfaPasses.clear();
	}

	public static XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (ProcedurePass procedurePass : procedurePasses) {
			if(!procedurePass.isPostInlining() || ProcedurePass.postInlining) builder = procedurePass.run(builder);
		}
		return builder;
	}

	public static XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		if(bottomUp) {
			builder.runProcedurePasses();
		}

		for (ProcessPass processPass : processPasses) {
			builder = processPass.run(builder);
		}

		if(!bottomUp) {
			builder.runProcedurePasses();
		}
		return builder;
	}

	public static XCFA.Builder run(XCFA.Builder builder) {
		if(bottomUp) {
			builder.runProcessPasses();
		}

		for (XcfaPass xcfaPass : xcfaPasses) {
			builder = xcfaPass.run(builder);
		}

		if(!bottomUp) {
			builder.runProcessPasses();
		}
		return builder;
	}
}
