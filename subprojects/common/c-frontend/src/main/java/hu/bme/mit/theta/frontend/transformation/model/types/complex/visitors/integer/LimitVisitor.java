package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CUnsignedShort;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class LimitVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, AssumeStmt> {
	public static final LimitVisitor instance = new LimitVisitor();

	@Override
	public AssumeStmt visit(CSignedShort type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("short");
		return Assume(And(
				Geq(param, Int(BigInteger.TWO.pow(width-1).negate())),
				Leq(param, Int(BigInteger.TWO.pow(width-1).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CUnsignedShort type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("short");
		return Assume(And(
				Geq(param, Int(0)),
				Leq(param, Int(BigInteger.TWO.pow(width).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(Fitsall type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("fitsall");
		return Assume(And(
				Geq(param, Int(BigInteger.TWO.pow(width-1).negate())),
				Leq(param, Int(BigInteger.TWO.pow(width-1).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CSignedLongLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("longlong");
		return Assume(And(
				Geq(param, Int(BigInteger.TWO.pow(width-1).negate())),
				Leq(param, Int(BigInteger.TWO.pow(width-1).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CUnsignedLongLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("longlong");
		return Assume(And(
				Geq(param, Int(0)),
				Leq(param, Int(BigInteger.TWO.pow(width).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CUnsignedLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("long");
		return Assume(And(
				Geq(param, Int(0)),
				Leq(param, Int(BigInteger.TWO.pow(width).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CSignedLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("long");
		return Assume(And(
				Geq(param, Int(BigInteger.TWO.pow(width-1).negate())),
				Leq(param, Int(BigInteger.TWO.pow(width-1).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CSignedInt type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("int");
		return Assume(And(
				Geq(param, Int(BigInteger.TWO.pow(width-1).negate())),
				Leq(param, Int(BigInteger.TWO.pow(width-1).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CUnsignedInt type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("int");
		return Assume(And(
				Geq(param, Int(0)),
				Leq(param, Int(BigInteger.TWO.pow(width).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CSignedChar type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("char");
		return Assume(And(
				Geq(param, Int(BigInteger.TWO.pow(width-1).negate())),
				Leq(param, Int(BigInteger.TWO.pow(width-1).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CUnsignedChar type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("char");
		return Assume(And(
				Geq(param, Int(0)),
				Leq(param, Int(BigInteger.TWO.pow(width).subtract(BigInteger.ONE)))));
	}

	@Override
	public AssumeStmt visit(CBool type, Expr<?> param) {
		return Assume(And(
				Geq(param, Int(0)),
				Leq(param, Int(1))));
	}
}
