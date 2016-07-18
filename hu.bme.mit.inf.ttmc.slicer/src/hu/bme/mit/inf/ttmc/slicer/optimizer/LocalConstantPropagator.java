package hu.bme.mit.inf.ttmc.slicer.optimizer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IffExpr;
import hu.bme.mit.inf.ttmc.core.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.VarRefExprVisitor;
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
import hu.bme.mit.inf.ttmc.slicer.cfg.BlockCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.BranchStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.BranchingBlockCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.SequentialStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.*;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.*;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.*;

public class LocalConstantPropagator implements CFGOptimizer {

	@Override
	public CFG transform(CFG input) {
		/*
		 * Perform simple local constant propagation in the given CFG.
		 */
		input.nodes().stream().filter(s -> s instanceof BlockCFGNode).forEach(node -> {
			BlockCFGNode newBlock = this.processBasicBlock((BlockCFGNode) node);
			node.replace(newBlock);
		});

		return input;
	}

	private BlockCFGNode processBasicBlock(BlockCFGNode node) {
		Map<VarDecl<? extends Type>, LitExpr<? extends Type>> constVars = new HashMap<>();
		ConstantFolderExprVisitor visitor = new ConstantFolderExprVisitor(constVars);
		List<Stmt> newBlock = new ArrayList<Stmt>();

		for (StmtCFGNode cn : node.getContainedNodes()) {
			Stmt s = cn.getStmt();
			if (s instanceof AssignStmt<?, ?>) {
				AssignStmt<? extends Type, ? extends Type> assign = (AssignStmt<? extends Type, ? extends Type>) s;
				Expr<? extends Type> expr = assign.getExpr().accept(visitor, null);
				if (expr instanceof LitExpr<?>) {
					// It is a constant, we can save it
					constVars.put(assign.getVarDecl(), (LitExpr<? extends Type>) expr);
				} else {
					// It does not contain a constant value, so it should not be present in the map
					constVars.remove(assign.getVarDecl());
				}

				if (expr != assign.getExpr()) {
					newBlock.add(Assign(assign.getVarDecl(), ExprUtils.cast(expr, assign.getVarDecl().getType().getClass())));
				} else {
					newBlock.add(s);
				}
			} else if (s instanceof AssumeStmt) {
				AssumeStmt assume = (AssumeStmt) s;
				Expr<? extends BoolType> cond = ExprUtils.cast(assume.getCond().accept(visitor, null), BoolType.class);

				newBlock.add(Assume(cond));
			} else if (s instanceof ReturnStmt<?>) {
				ReturnStmt<? extends Type> ret = (ReturnStmt<? extends Type>) s;
				Expr<? extends Type> expr = ret.getExpr().accept(visitor, null);

				newBlock.add(Return(expr));
			} else if (s instanceof AssertStmt) {
				AssertStmt assertStmt = (AssertStmt) s;
				Expr<? extends BoolType> cond = ExprUtils.cast(assertStmt.getCond().accept(visitor, null), BoolType.class);

				newBlock.add(Assert(cond));
			} else if (s instanceof HavocStmt<?>){
				newBlock.add(s);
			} else {
				throw new UnsupportedOperationException();
			}
			System.out.println(constVars);
		}

		if (newBlock.isEmpty()) {
			return node;
		}

		List<StmtCFGNode> newNodes = new ArrayList<StmtCFGNode>();
		Stmt head = newBlock.get(0);

		StmtCFGNode prev = head instanceof AssumeStmt
			? new BranchStmtCFGNode((AssumeStmt) head)
			: new SequentialStmtCFGNode(head);
		newNodes.add(prev);
		for (int i = 1; i < newBlock.size(); i++) {
			head = newBlock.get(i);
			StmtCFGNode curr = head instanceof AssumeStmt
				? new BranchStmtCFGNode((AssumeStmt) head)
				: new SequentialStmtCFGNode(head);
			prev.addChild(curr);
			newNodes.add(curr);
			prev = curr;
		}

		StmtCFGNode tail = newNodes.get(newNodes.size() - 1);
		if (tail instanceof BranchStmtCFGNode)
			return new BranchingBlockCFGNode(newNodes);

		return new BlockCFGNode(newNodes);
	}


}
