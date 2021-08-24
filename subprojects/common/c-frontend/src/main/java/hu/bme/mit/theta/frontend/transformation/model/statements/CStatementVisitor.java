package hu.bme.mit.theta.frontend.transformation.model.statements;

public interface CStatementVisitor<P, R> {
	R visit(CAssignment statement, P param);
	R visit(CAssume statement, P param);
	R visit(CBreak statement, P param);
	R visit(CCall statement, P param);
	R visit(CCase statement, P param);
	R visit(CCompound statement, P param);
	R visit(CContinue statement, P param);
	R visit(CDecls statement, P param);
	R visit(CDefault statement, P param);
	R visit(CDoWhile statement, P param);
	R visit(CExpr statement, P param);
	R visit(CFor statement, P param);
	R visit(CFunction statement, P param);
	R visit(CGoto statement, P param);
	R visit(CIf statement, P param);
	R visit(CInitializerList statement, P param);
	R visit(CProgram statement, P param);
	R visit(CRet statement, P param);
	R visit(CSwitch statement, P param);
	R visit(CWhile statement, P param);
}
