package hu.bme.mit.theta.solver.smtlib;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvToIntExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToBvExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatPosExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;

public class SmtLibExprTransformer {
    private static final int CACHE_SIZE = 1000;

    private final SmtLibTransformationManager transformer;

    private final Cache<Expr<?>, String> exprToTerm;
    private final DispatchTable<String> table;
    private final Env env;

    public SmtLibExprTransformer(final SmtLibTransformationManager transformer) {
        this.transformer = transformer;
        this.env = new Env();

        this.exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

        this.table = DispatchTable.<String>builder()

                // General

                .addCase(RefExpr.class, this::transformRef)

                .addCase(IteExpr.class, this::transformIte)

                // Boolean

                .addCase(FalseExpr.class, this::transformFalse)

                .addCase(TrueExpr.class, this::transformTrue)

                .addCase(NotExpr.class, this::transformNot)

                .addCase(ImplyExpr.class, this::transformImply)

                .addCase(IffExpr.class, this::transformIff)

                .addCase(XorExpr.class, this::transformXor)

                .addCase(AndExpr.class, this::transformAnd)

                .addCase(OrExpr.class, this::transformOr)

                .addCase(ExistsExpr.class, this::transformExists)

                .addCase(ForallExpr.class, this::transformForall)

                // Rationals

                .addCase(RatLitExpr.class, this::transformRatLit)

                .addCase(RatAddExpr.class, this::transformRatAdd)

                .addCase(RatSubExpr.class, this::transformRatSub)

                .addCase(RatPosExpr.class, this::transformRatPos)

                .addCase(RatNegExpr.class, this::transformRatNeg)

                .addCase(RatMulExpr.class, this::transformRatMul)

                .addCase(RatDivExpr.class, this::transformRatDiv)

                .addCase(RatEqExpr.class, this::transformRatEq)

                .addCase(RatNeqExpr.class, this::transformRatNeq)

                .addCase(RatGeqExpr.class, this::transformRatGeq)

                .addCase(RatGtExpr.class, this::transformRatGt)

                .addCase(RatLeqExpr.class, this::transformRatLeq)

                .addCase(RatLtExpr.class, this::transformRatLt)

                // Integers

                .addCase(IntLitExpr.class, this::transformIntLit)

                .addCase(IntAddExpr.class, this::transformIntAdd)

                .addCase(IntSubExpr.class, this::transformIntSub)

                .addCase(IntPosExpr.class, this::transformIntPos)

                .addCase(IntNegExpr.class, this::transformIntNeg)

                .addCase(IntMulExpr.class, this::transformIntMul)

                .addCase(IntDivExpr.class, this::transformIntDiv)

                .addCase(IntModExpr.class, this::transformIntMod)

                .addCase(IntRemExpr.class, this::transformIntRem)

                .addCase(IntEqExpr.class, this::transformIntEq)

                .addCase(IntNeqExpr.class, this::transformIntNeq)

                .addCase(IntGeqExpr.class, this::transformIntGeq)

                .addCase(IntGtExpr.class, this::transformIntGt)

                .addCase(IntLeqExpr.class, this::transformIntLeq)

                .addCase(IntLtExpr.class, this::transformIntLt)

                .addCase(IntToRatExpr.class, this::transformIntToRat)

                .addCase(IntToBvExpr.class, this::transformIntToBv)

                // Bitvectors

                .addCase(BvLitExpr.class, this::transformBvLit)

                .addCase(BvAddExpr.class, this::transformBvAdd)

                .addCase(BvSubExpr.class, this::transformBvSub)

                .addCase(BvPosExpr.class, this::transformBvPos)

                .addCase(BvNegExpr.class, this::transformBvNeg)

                .addCase(BvMulExpr.class, this::transformBvMul)

                .addCase(BvDivExpr.class, this::transformBvDiv)

                .addCase(BvModExpr.class, this::transformBvMod)

                .addCase(BvRemExpr.class, this::transformBvRem)

                .addCase(BvAndExpr.class, this::transformBvAnd)

                .addCase(BvOrExpr.class, this::transformBvOr)

                .addCase(BvXorExpr.class, this::transformBvXor)

                .addCase(BvNotExpr.class, this::transformBvNot)

                .addCase(BvShiftLeftExpr.class, this::transformBvShiftLeft)

                .addCase(BvArithShiftRightExpr.class, this::transformBvArithShiftRight)

                .addCase(BvLogicShiftRightExpr.class, this::transformBvLogicShiftRight)

                .addCase(BvRotateLeftExpr.class, this::transformBvRotateLeft)

                .addCase(BvRotateRightExpr.class, this::transformBvRotateRight)

                .addCase(BvEqExpr.class, this::transformBvEq)

                .addCase(BvNeqExpr.class, this::transformBvNeq)

                .addCase(BvGeqExpr.class, this::transformBvGeq)

                .addCase(BvGtExpr.class, this::transformBvGt)

                .addCase(BvLeqExpr.class, this::transformBvLeq)

                .addCase(BvLtExpr.class, this::transformBvLt)

                .addCase(BvToIntExpr.class, this::transformBvToInt)

                .build();
    }

    public final String toTerm(final Expr<?> expr) {
        try {
            return exprToTerm.get(expr, () -> table.dispatch(expr));
        } catch (final ExecutionException e) {
            throw new AssertionError();
        }
    }

    ////

    /*
     * General
     */

    protected String transformRef(final RefExpr<?> expr) {
        final Decl<?> decl = expr.getDecl();
        if (decl instanceof ConstDecl) {
            return transformer.toSymbol(decl);
        } else if (decl instanceof ParamDecl) {
            return (String) env.eval(DeclSymbol.of(decl));
        } else {
            throw new UnsupportedOperationException("Cannot transform reference for declaration: " + decl);
        }
    }

    protected String transformIte(final IteExpr<?> expr) {
        final String condTerm = toTerm(expr.getCond());
        final String thenTerm = toTerm(expr.getThen());
        final String elzeTerm = toTerm(expr.getElse());
        return String.format("(ite %s %s %s)", condTerm, thenTerm, elzeTerm);
    }

    /*
     * Booleans
     */

    protected String transformFalse(final FalseExpr expr) {
        return "false";
    }

    protected String transformTrue(final TrueExpr expr) {
        return "true";
    }

    protected String transformNot(final NotExpr expr) {
        return String.format("(not %s)", toTerm(expr.getOp()));
    }

    protected String transformImply(final ImplyExpr expr) {
        return String.format("(=> %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIff(final IffExpr expr) {
        return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformXor(final XorExpr expr) {
        return String.format("(xor %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformAnd(final AndExpr expr) {
        final String[] opTerms = expr.getOps().stream()
            .map(this::toTerm)
            .toArray(String[]::new);

        return String.format("(and %s)", String.join(" ", opTerms));
    }

    protected String transformOr(final OrExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(or %s)", String.join(" ", opTerms));
    }

    protected String transformExists(final ExistsExpr expr) {
        env.push();
        final String[] paramTerms = transformParamDecls(expr.getParamDecls());
        final String opTerm = toTerm(expr.getOp());
        final String result = String.format("(exists (%s) %s)", String.join(" ", paramTerms), opTerm);
        env.pop();
        return result;
    }

    protected String transformForall(final ForallExpr expr) {
        env.push();
        final String[] paramTerms = transformParamDecls(expr.getParamDecls());
        final String opTerm = toTerm(expr.getOp());
        final String result = String.format("(forall (%s) %s)", String.join(" ", paramTerms), opTerm);
        env.pop();
        return result;
    }

    private String[] transformParamDecls(final List<ParamDecl<?>> paramDecls) {
        final String[] paramTerms = new String[paramDecls.size()];
        int i = 0;
        for (final ParamDecl<?> paramDecl : paramDecls) {
            final String paramSymbol = transformParamDecl(paramDecl);
            paramTerms[i] = paramSymbol;
            env.define(DeclSymbol.of(paramDecl), paramSymbol);
            i++;
        }
        return paramTerms;
    }

    private String transformParamDecl(final ParamDecl<?> paramDecl) {
        final Type type = paramDecl.getType();
        if (type instanceof FuncType<?, ?>) {
            throw new UnsupportedOperationException("Only simple types are supported");
        } else {
            return String.format("(%s %s)", paramDecl.getName(), transformer.toSort(type));
        }
    }

    /*
     * Rationals
     */

    protected String transformRatLit(final RatLitExpr expr) {
        return String.format("(/ %d.0 %d.0)", expr.getNum(), expr.getDenom());
    }

    protected String transformRatAdd(final RatAddExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(+ %s)", String.join(" ", opTerms));
    }

    protected String transformRatSub(final RatSubExpr expr) {
        return String.format("(- %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatPos(final RatPosExpr expr) {
        return toTerm(expr.getOp());
    }

    protected String transformRatNeg(final RatNegExpr expr) {
        return String.format("(- %s)", toTerm(expr.getOp()));
    }

    protected String transformRatMul(final RatMulExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(* %s)", String.join(" ", opTerms));
    }

    protected String transformRatDiv(final RatDivExpr expr) {
        return String.format("(/ %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatEq(final RatEqExpr expr) {
        return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatNeq(final RatNeqExpr expr) {
        return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatGeq(final RatGeqExpr expr) {
        return String.format("(>= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatGt(final RatGtExpr expr) {
        return String.format("(> %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatLeq(final RatLeqExpr expr) {
        return String.format("(<= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformRatLt(final RatLtExpr expr) {
        return String.format("(< %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    /*
     * Integers
     */

    protected String transformIntLit(final IntLitExpr expr) {
        return Integer.toString(expr.getValue());
    }

    protected String transformIntAdd(final IntAddExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(+ %s)", String.join(" ", opTerms));
    }

    protected String transformIntSub(final IntSubExpr expr) {
        return String.format("(- %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntPos(final IntPosExpr expr) {
        return toTerm(expr.getOp());
    }

    protected String transformIntNeg(final IntNegExpr expr) {
        return String.format("(- %s)", toTerm(expr.getOp()));
    }

    protected String transformIntMul(final IntMulExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(* %s)", String.join(" ", opTerms));
    }

    protected String transformIntDiv(final IntDivExpr expr) {
        return String.format("(/ %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntMod(final IntModExpr expr) {
        return String.format("(mod %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntRem(final IntRemExpr expr) {
        return String.format("(rem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntEq(final IntEqExpr expr) {
        return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntNeq(final IntNeqExpr expr) {
        return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntGeq(final IntGeqExpr expr) {
        return String.format("(>= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntGt(final IntGtExpr expr) {
        return String.format("(> %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntLeq(final IntLeqExpr expr) {
        return String.format("(<= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntLt(final IntLtExpr expr) {
        return String.format("(< %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformIntToRat(final IntToRatExpr expr) {
        return String.format("(to_real %s)", toTerm(expr.getOp()));
    }

    protected String transformIntToBv(final IntToBvExpr expr) {
        throw new UnsupportedOperationException("SMT-LIB does not have the corresponding operation");
        /* Works with Z3, but it is not standard
        return String.format("((_ int2bv %d) %s)", expr.getType().getSize(), toTerm(expr.getOp()));
        */
    }

    /*
     * Bitvectors
     */

    protected String transformBvLit(final BvLitExpr expr) {
        final String value = Arrays.toString(expr.getValue())
            .replace("true", "1")
            .replace("false", "0")
            .replace("[", "")
            .replace("]", "")
            .replace(",", "")
            .replace(" ", "");

        return String.format("#b%s", value);
    }

    protected String transformBvAdd(final BvAddExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(bvadd %s)", String.join(" ", opTerms));
    }

    protected String transformBvSub(final BvSubExpr expr) {
        return String.format("(bvsub %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformBvPos(final BvPosExpr expr) {
        return toTerm(expr.getOp());
    }

    protected String transformBvNeg(final BvNegExpr expr) {
        return String.format("(bvneg %s)", toTerm(expr.getOp()));
    }

    protected String transformBvMul(final BvMulExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(bvmul %s)", String.join(" ", opTerms));
    }

    protected String transformBvDiv(final BvDivExpr expr) {
        if(expr.getType().isSigned()) {
            return String.format("(bvsdiv %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvudiv %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvMod(final BvModExpr expr) {
        if(expr.getType().isSigned()) {
            return String.format("(bvsmod %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvurem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvRem(final BvRemExpr expr) {
        if(expr.getType().isSigned()) {
            return String.format("(bvsrem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvurem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvAnd(final BvAndExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(bvand %s)", String.join(" ", opTerms));
    }

    protected String transformBvOr(final BvOrExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(bvor %s)", String.join(" ", opTerms));
    }

    protected String transformBvXor(final BvXorExpr expr) {
        final String[] opTerms = expr.getOps().stream()
                .map(this::toTerm)
                .toArray(String[]::new);

        return String.format("(bvxor %s)", String.join(" ", opTerms));
    }

    protected String transformBvNot(final BvNotExpr expr) {
        return String.format("(bvnot %s)", toTerm(expr.getOp()));
    }

    protected String transformBvShiftLeft(final BvShiftLeftExpr expr) {
        return String.format("(bvshl %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformBvArithShiftRight(final BvArithShiftRightExpr expr) {
        return String.format("(bvashr %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformBvLogicShiftRight(final BvLogicShiftRightExpr expr) {
        return String.format("(bvlshr %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformBvRotateLeft(final BvRotateLeftExpr expr) {
        return String.format("((_ rotate_left %s) %s)", toTerm(expr.getRightOp()), toTerm(expr.getLeftOp()));
    }

    protected String transformBvRotateRight(final BvRotateRightExpr expr) {
        return String.format("((_ rotate_right %s) %s)", toTerm(expr.getRightOp()), toTerm(expr.getLeftOp()));
    }

    protected String transformBvEq(final BvEqExpr expr) {
        return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformBvNeq(final BvNeqExpr expr) {
        return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }

    protected String transformBvGeq(final BvGeqExpr expr) {
        if(expr.getLeftOp().getType().isSigned()) {
            return String.format("(bvsge %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvuge %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvGt(final BvGtExpr expr) {
        if(expr.getLeftOp().getType().isSigned()) {
            return String.format("(bvsgt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvugt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvLeq(final BvLeqExpr expr) {
        if(expr.getLeftOp().getType().isSigned()) {
            return String.format("(bvsle %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvule %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvLt(final BvLtExpr expr) {
        if(expr.getLeftOp().getType().isSigned()) {
            return String.format("(bvslt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
        else {
            return String.format("(bvult %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
        }
    }

    protected String transformBvToInt(final BvToIntExpr expr) {
        throw new UnsupportedOperationException("SMT-LIB does not have the corresponding operation");
        /* Works with Z3, but not standard
        if(expr.getOp().getType().isSigned()) {
            final String bv = toTerm(expr.getOp());
            final BigInteger exp = BigInteger.TWO.pow(expr.getOp().getType().getSize());
            return String.format(
                "(ite (bvslt %s ((_ int2bv %d) 0)) (- (bv2int %s) %s) (bv2int %s))",
                bv, expr.getOp().getType().getSize(), bv, exp.toString(), bv
            );
        }
        else {
            return String.format("(bv2int %s)", toTerm(expr.getOp()));
        }
        */
    }
}
