package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.mdd.MddBuilder;
import hu.bme.mit.delta.mdd.MddFactory;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Optional;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class ExpressionNodeUtils {

    private static UniqueTable<MddSymbolicNode> uniqueTable = UniqueTable.newInstance((a, b) -> a.getSymbolicRepresentation().equals(b.getSymbolicRepresentation()), n -> n.getSymbolicRepresentation().hashCode());

    private static MddSymbolicNode  terminalOne = new MddSymbolicNode(new Pair<>(True(), null),null,0);

    public static void cacheModel(MddSymbolicNode rootNode, Valuation valuation){
        MddSymbolicNode node = rootNode;
        Expr expr = ((Pair<Expr<BoolType>, MddVariable>)node.getSymbolicRepresentation()).first;
        MddVariable variable = node.getVariable();

        while(variable != null){

            final Optional<? extends MddVariable> lower = variable.getLower();
            final Decl decl = variable.getTraceInfo(Decl.class);
            final Optional<LitExpr<?>> literal = valuation.eval(decl);

            if(literal.isPresent()){
                final MutableValuation val = new MutableValuation();

                val.put(decl, literal.get());
                expr = ExprUtils.simplify(expr, val);

                if(lower.isPresent()){
                    MddSymbolicNode childNode;
                    if(node.getCacheView().containsKey(LitExprConverter.toInt(literal.get()))){
                        // Existing cached child
                        childNode = node.getCacheView().get(LitExprConverter.toInt(literal.get()));
                        assert childNode.isOn(lower.get());
                    } else {
                        // New child
                        // TODO hashcode
                        childNode = uniqueTable.checkIn(new MddSymbolicNode(new Pair<>((Expr<BoolType>) expr,lower.get()),lower.get().getLevel(),0));
                        node.cacheNode(LitExprConverter.toInt(literal.get()),childNode);
                    }
                    node = childNode;
                    variable = lower.get();

                } else {
                    if(expr instanceof TrueExpr){
                        node.cacheNode(LitExprConverter.toInt(literal.get()), terminalOne);
                    } else {
                        node.cacheNode(LitExprConverter.toInt(literal.get()),null);
                    }
                    // TODO itt mi van?
                    variable = null;
                }


            } else {
                // TODO ilyenkor bármi lehet az értéke
                // máshogy kell kezelni ha azért mert nincs benne a kifejezésben, meg ha azért mert minden behelyettesítésére igaz
            }
        }
    }

}
