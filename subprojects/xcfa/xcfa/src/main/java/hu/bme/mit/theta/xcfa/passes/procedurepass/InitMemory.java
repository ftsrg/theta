package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class InitMemory extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		final Set<Object> dereferencedVars = FrontendMetadata.lookupMetadata("dereferenced", true);
		final Set<Object> memories = dereferencedVars.stream().map(o -> FrontendMetadata.getMetadataValue(o, "refSubstitute")).filter(Optional::isPresent).map(Optional::get).collect(Collectors.toSet());
		final List<XcfaLabel> stms = new ArrayList<>();
		for (Object memoryO : memories) {
			addInit(stms, (VarDecl<ArrayType<Type, Type>>) memoryO);
		}
		for (XcfaEdge outgoingEdge : builder.getInitLoc().getOutgoingEdges()) {
			final List<XcfaLabel> newStmts = new ArrayList<>(stms);
			newStmts.addAll(outgoingEdge.getLabels());
			builder.removeEdge(outgoingEdge);
			builder.addEdge(outgoingEdge.withLabels(newStmts));
		}
		return builder;
	}

	private <E extends Type, T extends Type> void addInit(final List<XcfaLabel> stms, final VarDecl<ArrayType<E, T>> memory) {
		final Optional<Object> defaultElement = FrontendMetadata.getMetadataValue(memory, "defaultElement");
		if(defaultElement.isPresent() && defaultElement.get() instanceof LitExpr) {
			stms.add(Stmt(Assign(memory, ArrayLitExpr.of(List.of(), (LitExpr<T>)defaultElement.get(), memory.getType()))));
		}
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}