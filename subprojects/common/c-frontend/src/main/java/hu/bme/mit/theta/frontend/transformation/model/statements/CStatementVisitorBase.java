package hu.bme.mit.theta.frontend.transformation.model.statements;

public abstract class CStatementVisitorBase<P, R> implements CStatementVisitor<P, R> {
	public R visit(CAssignment statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CAssume statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CBreak statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CCall statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CCase statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CCompound statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CContinue statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CDecls statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CDefault statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CDoWhile statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CExpr statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CFor statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CFunction statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CGoto statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CIf statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CInitializerList statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CProgram statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CRet statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CSwitch statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}

	public R visit(CWhile statement, P param) {
		throw new UnsupportedOperationException("Not implemented");
	}
}
