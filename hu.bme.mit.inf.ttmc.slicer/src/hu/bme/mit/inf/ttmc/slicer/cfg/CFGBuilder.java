package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.common.Product2;
import hu.bme.mit.inf.ttmc.common.Tuple;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
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

import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.*;

public class CFGBuilder {

	public static class StmtToCFGTransformer implements StmtVisitor<CFGNode, CFGNode>
	{
		private CFG cfg;

		public StmtToCFGTransformer(CFG cfg) {
			this.cfg = cfg;
		}

		public void transform(Stmt stmt) {

			CFGNode node = new StmtCFGNode(stmt);
			node.addParent(cfg.getEntry());
			node.addChild(cfg.getExit());

			processStmt(stmt, node);
		}

		private void processStmt(Stmt stmt, CFGNode node) {
			if (stmt instanceof BlockStmt) {
				BlockStmt block = (BlockStmt) stmt;
				processBlockStmt(block, node);
			} /* else if (stmt instanceof DeclStmt<?, ?>) {
				DeclStmt<? extends Type, ? extends Type> decl = (DeclStmt<? extends Type, ? extends Type>) stmt;
				if (decl.getInitVal().isPresent()) {
					// This is an assignment
					Expr<Type> init = decl.getInitVal().get();
					Stmt assign = Assign(decl.getVarDecl(), decl.getInitVal().get());
				}
			} */else {
				stmt.accept(this, node);
			}
		}

		private void processBlockStmt(BlockStmt stmt, CFGNode node) {
			List<? extends Stmt> stmts = stmt.getStmts();

			Stmt head = stmts.get(0);
			List<? extends Stmt> tail = stmts.subList(1, stmts.size());

			CFGNode headNode = new StmtCFGNode(head);

			node.parentsReplace(headNode);
			if (tail.size() == 0) {
				node.childrenReplace(headNode);
				processStmt(head, headNode);
				return;
			}

			BlockStmt tailBlock = Block(tail);
			CFGNode tailNode = new StmtCFGNode(tailBlock);

			headNode.addChild(tailNode);

			node.childrenReplace(tailNode);
			processStmt(head, headNode);

			processBlockStmt(tailBlock, tailNode);
		}

		@Override
		public CFGNode visit(SkipStmt stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <DeclType extends Type, ExprType extends DeclType> CFGNode visit(DeclStmt<DeclType, ExprType> stmt,
				CFGNode param) {
			CFGNode node;
			if (stmt.getInitVal().isPresent()) {
				node = new StmtCFGNode(Assign(stmt.getVarDecl(), stmt.getInitVal().get()));
			} else {
				node = new StmtCFGNode(Havoc(stmt.getVarDecl()));
			}

			param.replace(node);

			return null;
		}

		@Override
		public CFGNode visit(AssumeStmt stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CFGNode visit(AssertStmt stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <DeclType extends Type, ExprType extends DeclType> CFGNode visit(AssignStmt<DeclType, ExprType> stmt,
				CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <DeclType extends Type> CFGNode visit(HavocStmt<DeclType> stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CFGNode visit(BlockStmt stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public <ReturnType extends Type> CFGNode visit(ReturnStmt<ReturnType> stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CFGNode visit(IfStmt stmt, CFGNode param) {
			Stmt assume = Assume(stmt.getCond());
			Stmt then = stmt.getThen();

			CFGNode assumeNode = new StmtCFGNode(assume);
			CFGNode thenNode = new StmtCFGNode(then);

			for (CFGNode child : param.getChildren()) {
				child.addParent(assumeNode);
			}

			param.parentsReplace(assumeNode);
			param.childrenReplace(thenNode);
			assumeNode.addChild(thenNode);
			processStmt(then, thenNode);

			return assumeNode;
		}

		@Override
		public CFGNode visit(IfElseStmt stmt, CFGNode param) {
			Stmt assume = Assume(stmt.getCond());
			Stmt then = stmt.getThen();
			Stmt elze = stmt.getElse();

			CFGNode assumeNode = new StmtCFGNode(assume);
			CFGNode thenNode = new StmtCFGNode(then);
			CFGNode elzeNode = new StmtCFGNode(elze);

			for (CFGNode child : param.getChildren()) {
				child.addParent(thenNode);
				child.addParent(elzeNode);
				child.removeParent(param);
			}

			param.parentsReplace(assumeNode);
			assumeNode.addChild(thenNode);
			assumeNode.addChild(elzeNode);
			processStmt(then, thenNode);
			processStmt(elze, elzeNode);

			return assumeNode;
		}

		@Override
		public CFGNode visit(WhileStmt stmt, CFGNode param) {
			Stmt assume = Assume(stmt.getCond());
			Stmt body = stmt.getDo();

			CFGNode assumeNode = new StmtCFGNode(assume);
			CFGNode bodyNode = new StmtCFGNode(body);


			param.parentsReplace(assumeNode);
			param.childrenReplace(assumeNode);
			assumeNode.addChild(bodyNode);
			bodyNode.addChild(assumeNode);
			processStmt(body, bodyNode);

			return assumeNode;

		}

		@Override
		public CFGNode visit(DoStmt stmt, CFGNode param) {
			// TODO Auto-generated method stub
			return null;
		}
	}

	public static CFG createCFG(ProcDecl<? extends Type> proc)
	{
		Stmt stmt = proc.getStmt().get();

		CFGNode entry = new DecoratedCFGNode("entry");
		CFGNode exit  = new DecoratedCFGNode("exit");

		CFG cfg = new CFG(entry, exit);

		StmtToCFGTransformer transformer = new StmtToCFGTransformer(cfg);
		transformer.transform(stmt);

		return cfg;

	}

}
