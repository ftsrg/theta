package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Optional;

public class ExpressionNodeUtils {

    private static UniqueTable<ExpressionNode> uniqueTable = UniqueTable.newInstance((a,b) -> a.getDecision().equals(b.getDecision()),n -> n.getDecision().hashCode());

    public static void cacheModel(ExpressionNode rootNode, Valuation valuation){
        ExpressionNode node = rootNode;
        Expr<BoolType> expr = node.getDecision().first;
        MddVariable variable = node.getDecision().second;

        while(variable != null){

            final Optional<? extends MddVariable> lower = variable.getLower();
            final Decl decl = variable.getTraceInfo(Decl.class);
            final Optional<LitExpr<?>> literal = valuation.eval(decl);

            if(literal.isPresent()){
                final MutableValuation val = new MutableValuation();

                val.put(decl, literal.get());
                expr = ExprUtils.simplify(expr, val);

                if(lower.isPresent()){
                    ExpressionNode childNode;
                    if(node.getCacheView().containsKey(LitExprConverter.toInt(literal.get()))){
                        // Existing cached child
                        childNode = node.getCacheView().get(LitExprConverter.toInt(literal.get()));
                        assert childNode.isOn(lower.get());
                    } else {
                        // New child
                        // TODO hashcode
                        childNode = uniqueTable.checkIn(new ExpressionNode(new Pair<>(expr,lower.get()),lower.get().getLevel(),0));
                        node.cacheNode(LitExprConverter.toInt(literal.get()),childNode);
                    }
                    node = childNode;
                    variable = lower.get();

                } else {
                    // TODO itt mi van?
                    node.cacheNode(LitExprConverter.toInt(literal.get()),null);
                }


            } else {
                // TODO ilyenkor bármi lehet az értéke
                // máshogy kell kezelni ha azért mert nincs benne a kifejezésben, meg ha azért mert minden behelyettesítésére igaz
            }
        }
    }

}
