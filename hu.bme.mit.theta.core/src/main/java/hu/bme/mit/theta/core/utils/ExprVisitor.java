package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IntDivExpr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.ModExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.RatDivExpr;
import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.expr.RemExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;

public interface ExprVisitor<P, R> {

	<DeclType extends Type> R visit(RefExpr<DeclType> expr, P param);

	<ExprType extends Type> R visit(PrimedExpr<ExprType> expr, P param);

	R visit(FalseExpr expr, P param);

	R visit(TrueExpr expr, P param);

	R visit(NotExpr expr, P param);

	R visit(ImplyExpr expr, P param);

	R visit(IffExpr expr, P param);

	R visit(AndExpr expr, P param);

	R visit(OrExpr expr, P param);

	R visit(ExistsExpr expr, P param);

	R visit(ForallExpr expr, P param);

	R visit(EqExpr expr, P param);

	R visit(NeqExpr expr, P param);

	R visit(GeqExpr expr, P param);

	R visit(GtExpr expr, P param);

	R visit(LeqExpr expr, P param);

	R visit(LtExpr expr, P param);

	R visit(IntLitExpr expr, P param);

	R visit(IntDivExpr expr, P param);

	R visit(RemExpr expr, P param);

	R visit(ModExpr expr, P param);

	R visit(RatLitExpr expr, P param);

	R visit(RatDivExpr expr, P param);

	<ExprType extends ClosedUnderNeg> R visit(NegExpr<ExprType> expr, P param);

	<ExprType extends ClosedUnderSub> R visit(SubExpr<ExprType> expr, P param);

	<ExprType extends ClosedUnderAdd> R visit(AddExpr<ExprType> expr, P param);

	<ExprType extends ClosedUnderMul> R visit(MulExpr<ExprType> expr, P param);

	<IndexType extends Type, ElemType extends Type> R visit(ArrayReadExpr<IndexType, ElemType> expr, P param);

	<IndexType extends Type, ElemType extends Type> R visit(ArrayWriteExpr<IndexType, ElemType> expr, P param);

	<ParamType extends Type, ResultType extends Type> R visit(FuncLitExpr<ParamType, ResultType> expr, P param);

	<ParamType extends Type, ResultType extends Type> R visit(FuncAppExpr<ParamType, ResultType> expr, P param);

	<ReturnType extends Type> R visit(ProcCallExpr<ReturnType> expr, P param);

	<ExprType extends Type> R visit(IteExpr<ExprType> expr, P param);
}