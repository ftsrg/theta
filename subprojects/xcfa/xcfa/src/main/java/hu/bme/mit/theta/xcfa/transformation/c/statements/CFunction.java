package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.passes.procedurepass.EmptyEdgeRemovalPass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CFunction extends CStatement{
	private final CDeclaration funcDecl;
	private final CStatement compound;
	private final List<VarDecl<?>> flatVariables;
	private final LinkedHashMap<String, XcfaLocation> locLut;
	public static LinkedHashMap<String, XcfaLocation> globalLocLut = null;

	public CFunction(CDeclaration funcDecl, CStatement compound, List<VarDecl<?>> flatVariables, LinkedHashMap<String, XcfaLocation> locLut) {
		this.funcDecl = funcDecl;
		this.compound = compound;
		this.flatVariables = flatVariables;
		this.locLut = locLut;
	}

	public CStatement getCompound() {
		return compound;
	}

	public CDeclaration getFuncDecl() {
		return funcDecl;
	}

	@Override
	public Object build(Object param) {
		checkState(param instanceof List && (((List<?>) param).size() == 0 || ((List<?>) param).get(0) instanceof Stmt), "Params for functions should be a list of init statements!");
		XcfaProcedure.Builder builder = XcfaProcedure.builder();
		globalLocLut = locLut;
		for (VarDecl<?> flatVariable : flatVariables) {
			builder.createVar(flatVariable, null);
		}
		builder.setRetType(funcDecl.getBaseType().isVoid() ? null : Int());
		builder.setName(funcDecl.getName());
		if(!funcDecl.getBaseType().isVoid()) {
			builder.createParam(XcfaProcedure.Direction.OUT, Var("ret", Int()));
		} else {
			builder.createParam(XcfaProcedure.Direction.OUT, Var("ret", Int()));
		}

		for (CDeclaration functionParam : funcDecl.getFunctionParams()) {
			checkState(functionParam.getBaseType().isVoid() ||  functionParam.getVarDecl() != null, "Function param should have an associated variable!");
			if(functionParam.getVarDecl() != null) builder.createParam(XcfaProcedure.Direction.IN, functionParam.getVarDecl());
		}
		XcfaLocation init = new XcfaLocation("init" + counter++, Map.of());
		builder.addLoc(init);
		builder.setInitLoc(init);
		if(((List<?>) param).size() > 0) {
			XcfaLocation endinit = new XcfaLocation("end_init" + counter++, Map.of());
			builder.addLoc(endinit);
			//noinspection unchecked
			XcfaEdge edge = new XcfaEdge(init, endinit, (List<Stmt>) param);
			builder.addEdge(edge);
			init = endinit;
		}
		XcfaLocation ret = new XcfaLocation("ret" + counter++, Map.of());
		builder.addLoc(ret);
		XcfaLocation end = compound.build(builder, init, null, null, ret);
		builder.addEdge(new XcfaEdge(end, ret, List.of()));
		builder.setFinalLoc(ret);
		builder = new EmptyEdgeRemovalPass().run(builder);
		return builder.build();
	}
}
