package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleTypeFactory;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.NamedType;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;

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
		XcfaMetadata.lookupMetadata(funcDecl).forEach((s, o) -> XcfaMetadata.create(this, s, o));
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
		builder.setRetType(funcDecl.getBaseType().getActualType() instanceof CVoid ? null : funcDecl.getBaseType().getActualType().getSmtType());
		builder.setName(funcDecl.getName());
		if(!(funcDecl.getBaseType().getActualType() instanceof CVoid)) {
			VarDecl<?> var = Var(funcDecl.getName() + "_ret" + counter++, funcDecl.getBaseType().getActualType().getSmtType());
			XcfaMetadata.create(var.getRef(), "cType", funcDecl.getBaseType().getActualType());
			builder.createParam(XcfaProcedure.Direction.OUT, var);
		} else {
			// TODO we assume later, that there is always a ret var, but this should change
			VarDecl<?> var = Var(funcDecl.getName() + "_ret" + counter++, funcDecl.getBaseType().getActualType().getSmtType());
			NamedType signedIntType = CSimpleTypeFactory.NamedType("int");
			signedIntType.setSigned(true);
			XcfaMetadata.create(var.getRef(), "cType", signedIntType);
			builder.createParam(XcfaProcedure.Direction.OUT, var);
		}

		for (CDeclaration functionParam : funcDecl.getFunctionParams()) {
			checkState(functionParam.getBaseType().getActualType() instanceof CVoid ||  functionParam.getVarDecl() != null, "Function param should have an associated variable!");
			if(functionParam.getVarDecl() != null) builder.createParam(XcfaProcedure.Direction.IN, functionParam.getVarDecl());
		}
		XcfaLocation init = new XcfaLocation("init" + counter++, Map.of());
		builder.addLoc(init);
        propagateMetadata(init);
		builder.setInitLoc(init);
		if(((List<?>) param).size() > 0 && builder.getName().equals("main")) {
			XcfaLocation endinit = new XcfaLocation("end_init" + counter++, Map.of());
			builder.addLoc(endinit);
        	propagateMetadata(endinit);
			//noinspection unchecked
			XcfaEdge edge = new XcfaEdge(init, endinit, (List<Stmt>) param);
			builder.addEdge(edge);
        	propagateMetadata(edge);
			init = endinit;
		}
		XcfaLocation ret = new XcfaLocation("ret" + counter++, Map.of());
		builder.addLoc(ret);
        propagateMetadata(ret);
		XcfaLocation end = compound.build(builder, init, null, null, ret);
		XcfaEdge edge = new XcfaEdge(end, ret, List.of());
		builder.addEdge(edge);
        propagateMetadata(edge);
		builder.setFinalLoc(ret);
		return builder.build();
	}
}
