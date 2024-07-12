package hu.bme.mit.theta.xsts.analysis;

import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddToStructuralTransformer;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.DomainSize;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.xsts.analysis.RandomXstsKt.generateXsts;
import static org.junit.Assert.assertTrue;

@RunWith(value = org.junit.runners.Parameterized.class)
public class XstsMddStructuralSymbolicComparisonTest {

    private static final int iterations = 5;
    private static final int upperbound = 5;

    @Parameterized.Parameter(value = 0)
    public int seed;

    @Parameterized.Parameters(name = "{index}: {0}")
    public static List<Object[]> data() {
        return IntStream.range(0, iterations)
                .mapToObj(i -> new Object[]{i})
                .collect(Collectors.toList());
    }

    @Test
    public void test() throws Exception {

        try(var pool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            var xsts = generateXsts(seed);

            final MddGraph<Expr> transGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
            final MddGraph<Expr> structGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());

            final MddVariableOrder transOrder = JavaMddFactory.getDefault().createMddVariableOrder(transGraph);
            final MddVariableOrder structOrder = JavaMddFactory.getDefault().createMddVariableOrder(structGraph);

            final var tranToExprResult = StmtUtils.toExpr(xsts.getTran(), VarIndexingFactory.indexing(0));

            final List<Expr<BoolType>> boundExprs = new ArrayList<>();
            final var shuffledVars = new ArrayList<>(xsts.getVars());
            Collections.shuffle(shuffledVars, new Random(seed));
            for (var v : shuffledVars) {
                final int domainSize = v.getType().getDomainSize() == DomainSize.INFINITY ? 0 : v.getType().getDomainSize().getFiniteSize().intValue();

                transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(tranToExprResult.getIndexing().get(v) == 0 ? 1 : tranToExprResult.getIndexing().get(v)), domainSize));
                transOrder.createOnTop(MddVariableDescriptor.create(v.getConstDecl(0), domainSize));

                structOrder.createOnTop(MddVariableDescriptor.create(v.getName() + "2", domainSize));
                structOrder.createOnTop(MddVariableDescriptor.create(v.getName(), domainSize));

                if (v.getType() instanceof hu.bme.mit.theta.core.type.inttype.IntType) {
                    boundExprs.add(Geq(v.getConstDecl(0).getRef(), Int(0)));
                    boundExprs.add(Leq(v.getConstDecl(0).getRef(), Int(upperbound)));
                    boundExprs.add(Geq(v.getConstDecl(tranToExprResult.getIndexing().get(v) == 0 ? 1 : tranToExprResult.getIndexing().get(v)).getRef(), Int(0)));
                    boundExprs.add(Leq(v.getConstDecl(tranToExprResult.getIndexing().get(v) == 0 ? 1 : tranToExprResult.getIndexing().get(v)).getRef(), Int(upperbound)));
                }
            }

            final var transSig = transOrder.getDefaultSetSignature();
            final var structSig = structOrder.getDefaultSetSignature();
            var stmtUnfold = PathUtils.unfold(tranToExprResult.getExprs().stream().findFirst().get(), 0);
            stmtUnfold = And(stmtUnfold, And(boundExprs));
            final MddHandle transitionNode = transSig.getTopVariableHandle().checkInNode(MddExpressionTemplate.of(stmtUnfold, o -> (Decl) o, pool));

            final MddHandle structuralTransitionNode = MddToStructuralTransformer.transform(transitionNode, structSig.getTopVariableHandle());

            final Long symbolicSize = calculateNonzeroCount(transitionNode);
            final Long structuralSize = calculateNonzeroCount(structuralTransitionNode);
            assertTrue(symbolicSize >= structuralSize);
        }

    }


    private static Long calculateNonzeroCount(MddHandle root) {
        if (root == null) {
            throw new IllegalArgumentException("Root handle cannot be null.");
        } else {
            int height = root.getVariableHandle().getHeight();
            Map<MddHandle, Long> cache = HashObjObjMaps.newMutableMap();
            Long ret = calculateNonzeroCount(root, height, cache, root.cursor());
            return ret;
        }
    }

    private static Long calculateNonzeroCount(MddHandle node, int level, Map<MddHandle, Long> cache, RecursiveIntObjCursor<? extends MddHandle> cursor) {
        Long cached = (Long) cache.getOrDefault(node, null);
        if (cached != null) {
            return cached;
        } else if (node.isTerminalZero()) {
            return 0L;
        } else if (node.isTerminal() && !node.isTerminalZero()) {
            assert level == 0;

            return 1L;
        } else {
            long ret = 0L;

            while (cursor.moveNext()) {
                try (var valueCursor = cursor.valueCursor()) {
                    Long res = calculateNonzeroCount(cursor.value(), level - 1, cache, valueCursor);
                    if (res == null) {
                        return null;
                    }
                    ret += res;
                }
            }

            Long lRet = ret;
            cache.put(node, lRet);
            return lRet;
        }
    }

}
