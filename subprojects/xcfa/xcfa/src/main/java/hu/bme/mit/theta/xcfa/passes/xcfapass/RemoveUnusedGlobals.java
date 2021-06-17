package hu.bme.mit.theta.xcfa.passes.xcfapass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class RemoveUnusedGlobals extends XcfaPass {
	@Override
	public XCFA.Builder run(XCFA.Builder builder) {
		Set<VarDecl<?>> usedGlobals = new LinkedHashSet<>();
		for (XcfaProcess process : builder.getProcesses()) {
			for (XcfaProcedure procedure : process.getProcedures()) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (Stmt stmt : edge.getStmts()) {
						usedGlobals.addAll(StmtUtils.getVars(stmt));
					}
				}
			}
		}
		Set<Map.Entry<VarDecl<?>, Optional<LitExpr<?>>>> newGlobals = builder.getGlobalVars().entrySet().stream().filter(varDeclOptionalEntry -> usedGlobals.contains(varDeclOptionalEntry.getKey())).collect(Collectors.toSet());
		builder.getGlobalVars().clear();
		for (Map.Entry<VarDecl<?>, Optional<LitExpr<?>>> newGlobal : newGlobals) {
			builder.addGlobalVar(newGlobal.getKey(), newGlobal.getValue().orElse(null));
		}
		return builder;
	}
}
