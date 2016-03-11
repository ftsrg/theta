package hu.bme.mit.inf.ttmc.constraint.utils;

import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IffExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;

public interface ExprVisitor<P, R> {

	public <DeclType extends Type> R visit(ConstRefExpr<DeclType> expr, P param);
	public <DeclType extends Type> R visit(ParamRefExpr<DeclType> expr, P param);
	
	public R visit(FalseExpr expr, P param);
	public R visit(TrueExpr expr, P param);
	public R visit(NotExpr expr, P param);
	public R visit(ImplyExpr expr, P param);
	public R visit(IffExpr expr, P param);
	public R visit(AndExpr expr, P param);
	public R visit(OrExpr expr, P param);
	
	public R visit(ExistsExpr expr, P param);
	public R visit(ForallExpr expr, P param);
	
	public R visit(EqExpr expr, P param);
	public R visit(NeqExpr expr, P param);
	public R visit(GeqExpr expr, P param);
	public R visit(GtExpr expr, P param);
	public R visit(LeqExpr expr, P param);
	public R visit(LtExpr expr, P param);
	
	public R visit(IntLitExpr expr, P param);
	public R visit(IntDivExpr expr, P param);
	public R visit(RemExpr expr, P param);
	public R visit(ModExpr expr, P param);
	
	public R visit(RatLitExpr expr, P param);
	public R visit(RatDivExpr expr, P param);
	
	public <ExprType extends ClosedUnderNeg> R visit(NegExpr<ExprType> expr, P param);
	public <ExprType extends ClosedUnderSub> R visit(SubExpr<ExprType> expr, P param);
	public <ExprType extends ClosedUnderAdd> R visit(AddExpr<ExprType> expr, P param);
	public <ExprType extends ClosedUnderMul> R visit(MulExpr<ExprType> expr, P param);
	
	public <IndexType extends Type, ElemType extends Type> R visit(ArrayReadExpr<IndexType, ElemType> expr, P param);
	public <IndexType extends Type, ElemType extends Type> R visit(ArrayWriteExpr<IndexType, ElemType> expr, P param);
	
	public <ParamType extends Type, ResultType extends Type> R visit(FuncLitExpr<ParamType, ResultType> expr, P param);
	public <ParamType extends Type, ResultType extends Type> R visit(FuncAppExpr<ParamType, ResultType> expr, P param);
		
	public <ExprType extends Type> R visit(IteExpr<ExprType> expr, P param);
}