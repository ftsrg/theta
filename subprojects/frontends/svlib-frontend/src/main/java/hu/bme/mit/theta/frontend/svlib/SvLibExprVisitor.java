package hu.bme.mit.theta.frontend.svlib;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Function;

// term / relationalTerm -> Expr<?>
final class SvLibExprVisitor extends SvLibBaseVisitor<Expr<?>> {

    private final XcfaProcedureBuilder procedure;
    private final Map<String, VarDecl<?>> declarations;

    SvLibExprVisitor(XcfaProcedureBuilder procedure, Map<String, VarDecl<?>> declarations) {
        this.procedure = procedure;
        this.declarations = declarations;
    }

    Expr<BoolType> boolExpr(SvLibParser.TermContext term) {
        return cast(visit(term), Bool());
    }

    Expr<IntType> intExpr(SvLibParser.TermContext term) {
        return cast(visit(term), Int());
    }

    Expr<BoolType> relationalBoolExpr(SvLibParser.RelationalTermContext term) {
        return cast(visit(term), Bool());
    }

    @Override
    public Expr<?> visitNormalRelationalTerm(SvLibParser.NormalRelationalTermContext ctx) {
        return visit(ctx.term());
    }

    @Override
    public Expr<?> visitApplicationRelationalTerm(SvLibParser.ApplicationRelationalTermContext ctx) {
        return application(ctx.qual_identifer().getText(), ctx.term());
    }

    @Override
    public Expr<?> visitOldRelationalTerm(SvLibParser.OldRelationalTermContext ctx) {
        return unsupported("relational term 'old'");
    }

    @Override
    public Expr<?> visitSpecConstantTerm(SvLibParser.SpecConstantTermContext ctx) {
        String value = ctx.spec_constant().getText();
        if (value.matches("-?[0-9]+")) {
            return Int(value);
        }
        return unsupported("spec constant '" + value + "'");
    }

    @Override
    public Expr<?> visitQualIdentifierTerm(SvLibParser.QualIdentifierTermContext ctx) {
        String identifier = ctx.qual_identifer().getText();
        return switch (identifier) {
            case "true" -> True();
            case "false" -> False();
            default -> resolveVar(identifier).getRef();
        };
    }

    @Override
    public Expr<?> visitApplicationTerm(SvLibParser.ApplicationTermContext ctx) {
        return application(ctx.qual_identifer().getText(), ctx.term());
    }

    @Override
    public Expr<?> visitLetTerm(SvLibParser.LetTermContext ctx) {
        return unsupported("term 'let'");
    }

    @Override
    public Expr<?> visitForallTerm(SvLibParser.ForallTermContext ctx) {
        return unsupported("term 'forall'");
    }

    @Override
    public Expr<?> visitExistsTerm(SvLibParser.ExistsTermContext ctx) {
        return unsupported("term 'exists'");
    }

    @Override
    public Expr<?> visitMatchTerm(SvLibParser.MatchTermContext ctx) {
        return unsupported("term 'match'");
    }

    @Override
    public Expr<?> visitAnnotatedTerm(SvLibParser.AnnotatedTermContext ctx) {
        return unsupported("term annotation");
    }

    private Expr<?> application(String operatorText, List<SvLibParser.TermContext> args) {
        String operator = operatorText;
        return switch (operator) {
            case "+" -> Add(args.stream().map(this::intExpr).toList());
            case "-" ->
                    args.size() == 1
                            ? Neg(intExpr(args.get(0)))
                            : foldInt(args, (left, right) -> Sub(left, right));
            case "*" -> Mul(args.stream().map(this::intExpr).toList());
            case "div" -> binaryInt(operator, args, (left, right) -> Div(left, right));
            case "mod" -> binaryInt(operator, args, (left, right) -> Mod(left, right));
            case "=" -> binaryInt(operator, args, (left, right) -> Eq(left, right));
            case "distinct" -> binaryInt(operator, args, (left, right) -> Neq(left, right));
            case "<" -> binaryInt(operator, args, (left, right) -> Lt(left, right));
            case "<=" -> binaryInt(operator, args, (left, right) -> Leq(left, right));
            case ">" -> binaryInt(operator, args, (left, right) -> Gt(left, right));
            case ">=" -> binaryInt(operator, args, (left, right) -> Geq(left, right));
            case "not" -> unaryBool(operator, args, expr -> Not(expr));
            case "and" -> And(args.stream().map(this::boolExpr).toList());
            case "or" -> Or(args.stream().map(this::boolExpr).toList());
            case "=>" -> binaryBool(operator, args, (left, right) -> Imply(left, right));
            default -> unsupported("term operator '" + operator + "'");
        };
    }

    //if op is -,(- a b c) --> [a, b, c], (left, right) -> Sub(left, right) -->Sub(Sub(a, b), c) means (a - b) - c
    private Expr<?> foldInt(
            List<SvLibParser.TermContext> args,
            BiFunction<Expr<IntType>, Expr<IntType>, Expr<?>> op) {
        Expr<?> acc = intExpr(args.get(0));
        for (int i = 1; i < args.size(); i++) {
            acc = op.apply(cast(acc, Int()), intExpr(args.get(i)));
        }
        return acc;
    }

    private Expr<?> binaryInt(
            String operator,
            List<SvLibParser.TermContext> args,
            BiFunction<Expr<IntType>, Expr<IntType>, Expr<?>> op) {
        if (args.size() != 2) {
            throw new IllegalStateException(
                    "Expected binary argument list for SV-LIB operator '" + operator + "'");
        }
        return op.apply(intExpr(args.get(0)), intExpr(args.get(1)));
    }

    private Expr<?> binaryBool(
            String operator,
            List<SvLibParser.TermContext> args,
            BiFunction<Expr<BoolType>, Expr<BoolType>, Expr<?>> op) {
        if (args.size() != 2) {
            throw new IllegalStateException(
                    "Expected binary argument list for SV-LIB operator '" + operator + "'");
        }
        return op.apply(boolExpr(args.get(0)), boolExpr(args.get(1)));
    }

    private Expr<?> unaryBool(
            String operator,
            List<SvLibParser.TermContext> args,
            Function<Expr<BoolType>, Expr<?>> op) {
        if (args.size() != 1) {
            throw new IllegalStateException(
                    "Expected unary argument list for SV-LIB operator '" + operator + "'");
        }
        return op.apply(boolExpr(args.get(0)));
    }

    //1. First, look for local variables within `procedure.getVars()`.
    //2. Then, look for variables within `declarations`.
    //3. If neither is found, throw an exception.
    private VarDecl<?> resolveVar(String symbol) {
        String name = symbol;
        VarDecl<?> variable = null;
        for (VarDecl<?> candidate : procedure.getVars()) {
            if (candidate.getName().equals(name)) {
                variable = candidate;
                break;
            }
        }
        if (variable == null) {
            variable = declarations.get(name);
        }
        if (variable == null) {
            throw new IllegalStateException("Unknown SV-LIB variable '" + name + "'");
        }
        return variable;
    }
}
