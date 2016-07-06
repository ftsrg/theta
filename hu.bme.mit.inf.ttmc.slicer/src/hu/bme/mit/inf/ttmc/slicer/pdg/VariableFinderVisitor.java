package hu.bme.mit.inf.ttmc.slicer.pdg;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.common.Product2;
import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
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
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;
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

public class VariableFinderVisitor implements StmtVisitor<Void, Void>, ExprVisitor<Set<VarDecl<? extends Type>>, Void>, VarRefExprVisitor<Set<VarDecl<? extends Type>>, Void>
{
	private Set<VarDecl<? extends Type>> leftVars = new HashSet<>();
	private Set<VarDecl<? extends Type>> rightVars = new HashSet<>();

	public Set<VarDecl<? extends Type>> getLeftVars() { return this.leftVars; }
	public Set<VarDecl<? extends Type>> getRightVars() { return this.rightVars; }

	@Override
	public <DeclType extends Type> Void visit(VarRefExpr<DeclType> expr, Set<VarDecl<? extends Type>> param) {
		param.add(expr.getDecl());

		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(ConstRefExpr<DeclType> expr, Set<VarDecl<? extends Type>> param) {
		return null;
	}
	@Override
	public <DeclType extends Type> Void visit(ParamRefExpr<DeclType> expr, Set<VarDecl<? extends Type>> param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public Void visit(FalseExpr expr, Set<VarDecl<? extends Type>> param) {
		return null;
	}
	@Override
	public Void visit(TrueExpr expr, Set<VarDecl<? extends Type>> param) {
		return null;
	}
	@Override
	public Void visit(NotExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(ImplyExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(IffExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(AndExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getOps().forEach(s -> s.accept(this, param));

		return null;
	}
	@Override
	public Void visit(OrExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getOps().forEach(s -> s.accept(this, param));
		return null;
	}
	@Override
	public Void visit(ExistsExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(ForallExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(EqExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(NeqExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(GeqExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(GtExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(LeqExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(LtExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(IntLitExpr expr, Set<VarDecl<? extends Type>> param) {
		return null;
	}
	@Override
	public Void visit(IntDivExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(RemExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(ModExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public Void visit(RatLitExpr expr, Set<VarDecl<? extends Type>> param) {
		return null;
	}
	@Override
	public Void visit(RatDivExpr expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public <ExprType extends ClosedUnderNeg> Void visit(NegExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);

		return null;
	}
	@Override
	public <ExprType extends ClosedUnderSub> Void visit(SubExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return null;
	}
	@Override
	public <ExprType extends ClosedUnderAdd> Void visit(AddExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		expr.getOps().forEach(s -> s.accept(this, param));

		return null;
	}
	@Override
	public <ExprType extends ClosedUnderMul> Void visit(MulExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		expr.getOps().forEach(s -> s.accept(this, param));

		return null;
	}
	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(ArrayReadExpr<IndexType, ElemType> expr,
			Set<VarDecl<? extends Type>> param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(ArrayWriteExpr<IndexType, ElemType> expr,
			Set<VarDecl<? extends Type>> param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(FuncLitExpr<ParamType, ResultType> expr,
			Set<VarDecl<? extends Type>> param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(FuncAppExpr<ParamType, ResultType> expr,
			Set<VarDecl<? extends Type>> param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public <ExprType extends Type> Void visit(IteExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public Void visit(SkipStmt stmt, Void param) {
		return null;
	}
	@Override
	public <DeclType extends Type, ExprType extends DeclType> Void visit(DeclStmt<DeclType, ExprType> stmt,
			Void param) {
		this.leftVars.add(stmt.getVarDecl());
		if (stmt.getInitVal().isPresent()) {
			stmt.getInitVal().get().accept(this, this.rightVars);
		}

		return null;
	}
	@Override
	public Void visit(AssumeStmt stmt, Void param) {
		Set<VarDecl<? extends Type>> vars = new HashSet<VarDecl<? extends Type>>();

		stmt.getCond().accept(this, vars);

		this.rightVars.addAll(vars);
		return null;
	}
	@Override
	public Void visit(AssertStmt stmt, Void param) {
		stmt.getCond().accept(this, this.rightVars);
		return null;
	}
	@Override
	public <DeclType extends Type, ExprType extends DeclType> Void visit(AssignStmt<DeclType, ExprType> stmt,
			Void param) {
		this.leftVars.add(stmt.getVarDecl());
		stmt.getExpr().accept(this, this.rightVars);

		return null;
	}
	@Override
	public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Void param) {
		this.leftVars.add(stmt.getVarDecl());

		return null;
	}
	@Override
	public Void visit(BlockStmt stmt, Void param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public <ReturnType extends Type> Void visit(ReturnStmt<ReturnType> stmt, Void param) {
		stmt.getExpr().accept(this, this.rightVars);

		return null;
	}
	@Override
	public Void visit(IfStmt stmt, Void param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public Void visit(IfElseStmt stmt, Void param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public Void visit(WhileStmt stmt, Void param) {
		throw new UnsupportedOperationException();
	}
	@Override
	public Void visit(DoStmt stmt, Void param) {
		throw new UnsupportedOperationException();
	}

	public static Set<VarDecl<? extends Type>> findLeftVars(Stmt stmt)
	{
		VariableFinderVisitor visitor = new VariableFinderVisitor();
		stmt.accept(visitor, null);

		return visitor.leftVars;
	}

	public static Set<VarDecl<? extends Type>> findRightVars(Stmt stmt)
	{
		VariableFinderVisitor visitor = new VariableFinderVisitor();
		stmt.accept(visitor, null);

		return visitor.rightVars;
	}


}
