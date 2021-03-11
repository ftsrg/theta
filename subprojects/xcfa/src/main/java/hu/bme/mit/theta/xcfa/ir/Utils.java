package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.XCFA;

import java.math.BigInteger;
import java.util.*;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

public class Utils {

    private static final int FLOAT_DIGITS = 5;

    public static VarDecl<?> createVariable(String name, IRType type) {
        Type t;
        switch (type) {
            case INTEGER32: t = Int();      break;
            case FLOAT64:   t = Rat();      break;
            default:
                throw new IllegalStateException("Unexpected value: " + type);
        }
        return Var(name, t);
    }

    public static LitExpr<?> createConstant(IRType type, String value) {
        switch (type) {
            case INTEGER32: return IntLitExpr.of(new BigInteger(value));
            case FLOAT64:
                float v = Float.parseFloat(value);
                return RatLitExpr.of(BigInteger.valueOf((long)(v*(1 << FLOAT_DIGITS))), BigInteger.valueOf(1 << FLOAT_DIGITS));
            default:
                throw new IllegalStateException("Unexpected value: " + type);
        }
    }

    public static Collection<String> handleProcedure(
            Tuple3<String, IRType, List<Tuple2<IRType, String>>> function,
            XCFA.Process.Procedure.Builder procedureBuilder,
            SSAProvider ssa,
            Map<String, VarDecl<?>> globalVarLut) {

        Map<String, VarDecl<?>> localVarLut = new HashMap<>();

        for (Tuple2<IRType, String> param : function.get3()) {
            VarDecl<?> var = createVariable(param.get2(), param.get1());
            procedureBuilder.createParam(var);
            localVarLut.put(param.get2(), var);
        }

        List<String> blocks = ssa.getBlocks(function.get1());
        Map<String, XCFA.Process.Procedure.Location> locationLut = new HashMap<>();
        for (String block : blocks) {
            XCFA.Process.Procedure.Location loc = new XCFA.Process.Procedure.Location(block, new HashMap<>());
            locationLut.put(block, loc);
        }

        for (String block : locationLut.keySet()) {
            Map<String, Expr<?>> valueLut = new HashMap<>();
            for (Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction : ssa.getInstructions(block)) {
                switch(instruction.get1()) {
                    case RET:
                        break;
                    case BR:
                        break;
                    case SWITCH:
                        break;
                    case ADD:
                        break;
                    case SUB:
                        break;
                    case MUL:
                        break;
                    case SDIV:
                        break;
                    case SREM:
                        break;
                    case ALLOCA:
                        break;
                    case LOAD:
                        break;
                    case STORE:
                        break;
                    case FENCE:
                        break;
                    case ICMP:
                        break;
                    case PHI:
                        break;
                    case CALL:
                        break;
                    default:
                        throw new IllegalStateException("Unexpected value: " + instruction.get1());
                }
            }
        }

    }

}
