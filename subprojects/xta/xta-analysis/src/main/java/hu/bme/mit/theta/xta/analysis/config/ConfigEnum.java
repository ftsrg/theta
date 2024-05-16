package hu.bme.mit.theta.xta.analysis.config;

import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;

public class ConfigEnum {
    public enum Domain {
        EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT
    }

    public enum Refinement {
        FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE, UCB,
        NWT_WP, NWT_SP, NWT_WP_LV, NWT_SP_LV, NWT_IT_WP, NWT_IT_SP, NWT_IT_WP_LV, NWT_IT_SP_LV
    }
    public enum InitPrec {
        EMPTY, ALLVARS, ALLASSUMES
    }
    public enum Search {
        BFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),

        DFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs()));

        public final ArgNodeComparators.ArgNodeComparator comparator;

        private Search(final ArgNodeComparators.ArgNodeComparator comparator) {
            this.comparator = comparator;
        }

    }
}
