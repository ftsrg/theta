package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.pred.ExprSplitters;

public class XstsConfigBuilder {

    public enum Domain {
        EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT
    }

    ;

    public enum Refinement {
        FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE
    }

    ;

    public enum Search {
        BFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),

        DFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs()));

        public final ArgNodeComparators.ArgNodeComparator comparator;

        private Search(final ArgNodeComparators.ArgNodeComparator comparator) {
            this.comparator = comparator;
        }

    }

    ;

    public enum PredSplit {
        WHOLE(ExprSplitters.whole()),

        CONJUNCTS(ExprSplitters.conjuncts()),

        ATOMS(ExprSplitters.atoms());

        public final ExprSplitters.ExprSplitter splitter;

        private PredSplit(final ExprSplitters.ExprSplitter splitter) {
            this.splitter = splitter;
        }
    }

    ;

}
