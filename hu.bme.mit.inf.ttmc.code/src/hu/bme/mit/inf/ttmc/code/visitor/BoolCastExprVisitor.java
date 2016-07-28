package hu.bme.mit.inf.ttmc.code.visitor;

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
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.VarRefExprVisitor;

public class BoolCastExprVisitor implements VarRefExprVisitor<Void, VarRefExpr<BoolType>> {

	@Override
	public <DeclType extends Type> VarRefExpr<BoolType> visit(ConstRefExpr<DeclType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <DeclType extends Type> VarRefExpr<BoolType> visit(ParamRefExpr<DeclType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(FalseExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(TrueExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(NotExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(ImplyExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(IffExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(AndExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(OrExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(ExistsExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(ForallExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(EqExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(NeqExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(GeqExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(GtExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(LeqExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(LtExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(IntLitExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(IntDivExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(RemExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(ModExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(RatLitExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarRefExpr<BoolType> visit(RatDivExpr expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ExprType extends ClosedUnderNeg> VarRefExpr<BoolType> visit(NegExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ExprType extends ClosedUnderSub> VarRefExpr<BoolType> visit(SubExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ExprType extends ClosedUnderAdd> VarRefExpr<BoolType> visit(AddExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ExprType extends ClosedUnderMul> VarRefExpr<BoolType> visit(MulExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> VarRefExpr<BoolType> visit(
			ArrayReadExpr<IndexType, ElemType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> VarRefExpr<BoolType> visit(
			ArrayWriteExpr<IndexType, ElemType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> VarRefExpr<BoolType> visit(
			FuncLitExpr<ParamType, ResultType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> VarRefExpr<BoolType> visit(
			FuncAppExpr<ParamType, ResultType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ExprType extends Type> VarRefExpr<BoolType> visit(IteExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <DeclType extends Type> VarRefExpr<BoolType> visit(VarRefExpr<DeclType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}


}
