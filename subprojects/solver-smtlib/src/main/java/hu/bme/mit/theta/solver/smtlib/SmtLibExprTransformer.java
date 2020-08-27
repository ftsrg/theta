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
import hu.bme.mit.theta.core.type.functype.FuncType;
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
}
