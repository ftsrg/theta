package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CProgram extends CStatement{
	private final List<CFunction> functions;
	private final List<Tuple2<CDeclaration, VarDecl<?>>> globalDeclarations;

	public CProgram() {
		this.functions = new ArrayList<>();
		this.globalDeclarations = new ArrayList<>();
	}

	public List<Tuple2<CDeclaration, VarDecl<?>>> getGlobalDeclarations() {
		return globalDeclarations;
	}

	public List<CFunction> getFunctions() {
		return functions;
	}

	@Override
	public Object build(Object param) {
		XCFA.Builder builder = XCFA.builder();
		builder.setDynamic(true);

		List<Stmt> initStmtList = new ArrayList<>();
		for (Tuple2<CDeclaration, VarDecl<?>> globalDeclaration : globalDeclarations) {
			CComplexType type = CComplexType.getType(globalDeclaration.get2().getRef());
			if(type instanceof CVoid || type instanceof CStruct) {
				System.err.println("WARNING: Not handling init expression of " + globalDeclaration.get1() + " as it is non initializable");
				continue;
			}
			builder.addGlobalVar(globalDeclaration.get2(), type.getNullValue());
			if(globalDeclaration.get1().getInitExpr() != null) {
				initStmtList.add(Assign(cast(globalDeclaration.get2(), globalDeclaration.get2().getType()), cast(type.castTo(globalDeclaration.get1().getInitExpr().getExpression()), globalDeclaration.get2().getType())));
			} else {
				initStmtList.add(Assign(cast(globalDeclaration.get2(), globalDeclaration.get2().getType()), cast(type.getNullValue(), globalDeclaration.get2().getType())));
			}
		}
		XcfaProcess.Builder procBuilder = XcfaProcess.builder();
		for (CFunction function : functions) {
			Object build = function.build(initStmtList);
			checkState(build instanceof XcfaProcedure, "Function builds should yield XcfaProcedures!");
			procBuilder.addProcedure((XcfaProcedure) build);
			if(((XcfaProcedure) build).getName().equals("main")) procBuilder.setMainProcedure((XcfaProcedure) build);
		}
		XcfaProcess mainproc = procBuilder.build();
		builder.addProcess(mainproc);
		builder.setMainProcess(mainproc);
		return builder.build();
	}
}
