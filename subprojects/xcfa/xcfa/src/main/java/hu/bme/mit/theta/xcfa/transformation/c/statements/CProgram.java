package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.processpass.FunctionInlining;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
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
			builder.addGlobalVar(globalDeclaration.get2(), Int(0));
			if(globalDeclaration.get1().getInitExpr() != null) {
				initStmtList.add(Assign(cast(globalDeclaration.get2(), Int()), cast(globalDeclaration.get1().getInitExpr().getExpression(), Int())));
			} else {
				initStmtList.add(Assign(cast(globalDeclaration.get2(), Int()), cast(Int(0), Int())));
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
