package hu.bme.mit.inf.ttmc.code.stmt.visitor;

import java.nio.CharBuffer;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DeclStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.SkipStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.WhileStmt;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public class PrintStmtVisitor implements StmtVisitor<StringBuilder, String> {

	private int depth = 0;
	
	@Override
	public String visit(SkipStmt stmt, StringBuilder param) {
		return stmt.toString();
	}

	@Override
	public String visit(AssumeStmt stmt, StringBuilder param) {
		return stmt.toString();
	}

	@Override
	public String visit(AssertStmt stmt, StringBuilder param) {
		return stmt.toString();
	}

	@Override
	public <DeclType extends Type, ExprType extends DeclType> String visit(AssignStmt<DeclType, ExprType> stmt,
			StringBuilder param) {
		return stmt.toString();
	}

	@Override
	public <DeclType extends Type> String visit(HavocStmt<DeclType> stmt, StringBuilder param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String visit(BlockStmt stmt, StringBuilder param) {
		
		param.append(CharBuffer.allocate(this.depth).toString().replace('\0', ' '));
		this.depth++;
		param.append("{\n");
		for (Stmt s : stmt.getStmts()) {
			param.append(CharBuffer.allocate(this.depth).toString().replace('\0', ' '));
			param.append(s.accept(this, new StringBuilder()));
			param.append('\n');
		}
		this.depth--;
		param.append(CharBuffer.allocate(this.depth).toString().replace('\0', ' '));
		param.append("}\n");

		return param.toString();
	}

	@Override
	public <ReturnType extends Type> String visit(ReturnStmt<ReturnType> stmt, StringBuilder param) {
		return stmt.toString();
	}

	@Override
	public String visit(IfStmt stmt, StringBuilder param) {
		param.append("If(" + stmt.getCond().toString() + ")\n");
		param.append(stmt.getThen().accept(this, new StringBuilder()));
		return param.toString();
	}

	@Override
	public String visit(IfElseStmt stmt, StringBuilder param) {
		param.append("If(" + stmt.getCond().toString() + ")\n");
		param.append(stmt.getThen().accept(this, new StringBuilder()));
		param.append(CharBuffer.allocate(this.depth).toString().replace('\0', ' '));
		param.append("Else\n");
		param.append(stmt.getElse().accept(this, new StringBuilder()));
		
		return param.toString();
	}

	@Override
	public String visit(WhileStmt stmt, StringBuilder param) {
		param.append("While(" + stmt.getCond().toString() + ")\n");
		param.append(stmt.getDo().accept(this, new StringBuilder()));
		return param.toString();
	}

	@Override
	public String visit(DoStmt stmt, StringBuilder param) {
		param.append(stmt.getDo().accept(this, new StringBuilder()));
		param.append("While(" + stmt.getCond().toString() + ")\n");
		return param.toString();
	}

	@Override
	public <DeclType extends Type, ExprType extends DeclType> String visit(DeclStmt<DeclType, ExprType> stmt,
			StringBuilder param) {
		return stmt.toString();
	}

	
}
