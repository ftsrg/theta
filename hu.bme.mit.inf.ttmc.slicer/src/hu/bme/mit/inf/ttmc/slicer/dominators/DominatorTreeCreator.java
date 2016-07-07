package hu.bme.mit.inf.ttmc.slicer.dominators;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;

public class DominatorTreeCreator {

	private static class NodeInfo
	{
		public int dfs = 0;
		public int parent = 0;
		public int sdom = 0;
		public int idom = 0;
		public CFGNode node;

		public NodeInfo(CFGNode node) {
			this.node = node;
		}

		@Override
		public String toString() {
			return dfs + " " + parent + " " + sdom;
		}

	}

	public static void dominatorTree(CFG cfg)
	{
		Map<CFGNode, NodeInfo> infoMap = new HashMap<>();
		Map<Integer, NodeInfo> vertexMap = new HashMap<>();
		Map<Integer, Set<Integer>> bucket = new HashMap<>();
		Map<Integer, Integer> domMap = new HashMap<>();
		Map<Integer, Integer> ancestor = new HashMap<>();

		for (CFGNode node : cfg.nodes()) {
			infoMap.put(node, new NodeInfo(node));
		}

		/*
		 * Step 1: Carry out a depth-first search of the problem graph.
		 * Number the vertices from 1 to n as they are reached during the search.
		 * Initialize the variables used in succeeding steps.
		 */
		int cnt = DFS(cfg.getEntry(), 0, infoMap, vertexMap);

		for (int i = 1; i <= cnt; ++i) {
			bucket.put(i, new HashSet<Integer>());
			ancestor.put(i, 0);
		}

		System.out.println(infoMap);
		System.out.println(cnt);

		for (int w = cnt; w > 1; --w) {
			NodeInfo wInfo = vertexMap.get(w);
			int p = wInfo.parent;

			/*
			 * Step 2: Compute the semidominators of all vertices.
			 * Carry out the computation vertex by vertex in decreasing order by number.
			 */
			for (CFGNode pred : vertexMap.get(w).node.getParents()) {
				NodeInfo vInfo = infoMap.get(pred);
				System.out.println(vertexMap.get(w).node + " " + pred + " " + vInfo);
				int u = eval(vInfo, ancestor, vertexMap);
				NodeInfo uInfo = vertexMap.get(u);

				if (wInfo.sdom > uInfo.sdom) {
					wInfo.sdom = uInfo.sdom;
				}

				bucket.get(wInfo.sdom).add(w);
				link(p, w, ancestor);
			}

			/*
			 * Step 3: Implicitly define the immediate dominator of each vertex.
			 */
			Iterator<Integer> iter = bucket.get(p).iterator();

			while (iter.hasNext()) {
				Integer v = iter.next();
				NodeInfo vInfo = vertexMap.get(v);
				int u = eval(vInfo, ancestor, vertexMap);
				NodeInfo uInfo = vertexMap.get(u);

				domMap.put(v, uInfo.sdom < vInfo.sdom ? u : p);
				vInfo.idom = uInfo.sdom < vInfo.sdom ? u : p;
				iter.remove();
			}
		}

		for (int w = 2; w <= cnt; ++w) {
			NodeInfo wInfo = vertexMap.get(w);
			if (wInfo.idom != vertexMap.get(wInfo.sdom).dfs) {
				wInfo.idom = vertexMap.get(wInfo.idom).idom;
			}
		}

		infoMap.get(cfg.getEntry()).idom = 0;

		for (NodeInfo info : infoMap.values()) {
			if (info.dfs == 1)
				continue;
			System.out.println(vertexMap.get(info.idom).node + " dom " + info.node);
		}
	}

	private static void link(int v, int w, Map<Integer, Integer> ancestor) { ancestor.put(v, w); }

	private static int eval(NodeInfo vInfo, Map<Integer, Integer> ancestor, Map<Integer, NodeInfo> vertexMap)
	{
		int a = ancestor.get(vInfo.dfs);
		int v = vInfo.dfs;

		while (a != 0) {
			if (vInfo.sdom > vertexMap.get(a).sdom) {
				v = a;
			}
			a = ancestor.get(a);
		}

		return v;
	}


	private static int DFS(CFGNode node, int cnt, Map<CFGNode, NodeInfo> infoMap, Map<Integer, NodeInfo> vertexMap)
	{
		NodeInfo info = infoMap.get(node);
		info.sdom = info.dfs = ++cnt;
		vertexMap.put(info.dfs, info);

		for (CFGNode child : node.getChildren()) {
			NodeInfo childInfo = infoMap.get(child);
			if (childInfo.sdom == 0) {
				childInfo.parent = info.dfs;
				cnt = DFS(child, cnt, infoMap, vertexMap);
			}
		}

		return cnt;
	}

}
