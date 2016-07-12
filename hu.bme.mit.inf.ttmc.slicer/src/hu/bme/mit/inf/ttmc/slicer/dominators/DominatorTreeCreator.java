package hu.bme.mit.inf.ttmc.slicer.dominators;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;

public class DominatorTreeCreator {

	private static class NodeInfo
	{
		public int dfs = 0;
		public int parent = 0;
		public int sdom = 0;
		public int idom = 0;
		public CFGNode node;
		public DominatorTreeNode domNode;

		public NodeInfo(CFGNode node) {
			this.node = node;
			this.domNode = new DominatorTreeNode(node);
		}

		@Override
		public String toString() {
			return dfs + " " + parent + " " + sdom;
		}
	}

	public static DominatorTree postDominatorTree(CFG cfg)
	{
		return buildTree(cfg, true);
	}

	public static DominatorTree dominatorTree(CFG cfg)
	{
		return buildTree(cfg, false);
	}

	private static DominatorTree buildTree(CFG cfg, boolean reverse)
	{
		Map<CFGNode, Set<CFGNode>> dominators = new HashMap<>();

		CFGNode root = reverse ? cfg.getExit() : cfg.getEntry();
		dominators.put(root, new HashSet<CFGNode>() {{
			add(root);
		}});

		List<CFGNode> nodes = new ArrayList<CFGNode>(cfg.nodes());

		for (CFGNode node : nodes) {
			if (node == root)
				continue;
			dominators.put(node, new HashSet<CFGNode>(nodes));
		}

		nodes.remove(root);
		boolean change = true;
		while (change) {
			change = false;

			for (CFGNode node : nodes) {
				Set<CFGNode> nodeDoms = new HashSet<>();
				nodeDoms.add(node);

				Iterator<CFGNode> iter = reverse ? node.getChildren().iterator() : node.getParents().iterator();
				CFGNode first = iter.next();
				Set<CFGNode> parentDoms = new HashSet<>(dominators.get(first));
				//System.out.println("Node: " + node);
				//System.out.println("    " + first + ": " + parentDoms);
				while (iter.hasNext()) {
					CFGNode next = iter.next();
					parentDoms.retainAll(dominators.get(next));
					//System.out.println("    " + next + ": " + parentDoms);
				}

				nodeDoms.addAll(parentDoms);

				if (!dominators.get(node).equals(nodeDoms)) {
					dominators.put(node, nodeDoms);
					change = true;
				}
			}
		}

		// Find immediate dominators
		// p is immediate dominator of q (p idom q), if:
		//	1. p dom q
		//	2. every other dominator of q dominates p

		Map<CFGNode, DominatorTreeNode> domMapping = new HashMap<>();
		for (CFGNode node : nodes) {
			domMapping.put(node, new DominatorTreeNode(node));
		}
		domMapping.put(root, new DominatorTreeNode(root));


		dominators.forEach((CFGNode node, Set<CFGNode> doms) -> {
			// Node: The node being checked
			// Doms: The dominators of this node

			for (CFGNode dominator : doms) {
				if (dominator == node)
					continue;

				boolean isIdom = true;

				// Is this node an immediate dominator?
				// 	It is immediate if all other dominators of this node dominate it.
				for (CFGNode otherDominator : doms) {
					if (otherDominator == node || otherDominator == dominator)
						continue;


					if (!dominators.get(dominator).contains(otherDominator)) {
						isIdom = false;
						break;
					}
				}

				if (isIdom) {
					domMapping.get(node).setParent(domMapping.get(dominator));
					break;
				}

			}

		});

		return new DominatorTree(domMapping.get(root), domMapping);
	}

	/**
	 * Builds a dominator tree using the Lengauer-Tarjan algorithm
	 * @param cfg
	 */
	private static DominatorTree buildTreeOld(CFG cfg, boolean reverse)
	{
		Map<CFGNode, NodeInfo> infoMap = new HashMap<>();
		List<NodeInfo> vertices = new ArrayList<>();
		Map<Integer, Set<Integer>> bucket = new HashMap<>();

		for (CFGNode node : cfg.nodes()) {
			infoMap.put(node, new NodeInfo(node));
		}
		vertices.add(null); // Add a special node to indicate start
		CFGNode root = reverse ? cfg.getExit() : cfg.getEntry();

		/*
		 * Step 1: Carry out a depth-first search of the problem graph.
		 * Number the vertices from 1 to n as they are reached during the search.
		 * Initialize the variables used in succeeding steps.
		 */
		int cnt = DFS(root, 0, infoMap, vertices, reverse);

		int[] ancestor = new int[cnt + 1];

		for (int i = 1; i <= cnt; ++i) {
			bucket.put(i, new HashSet<Integer>());
		}

		for (int w = cnt; w > 1; --w) {
			NodeInfo wInfo = vertices.get(w);
			int p = wInfo.parent;

			/*
			 * Step 2: Compute the semidominators of all vertices.
			 * Carry out the computation vertex by vertex in decreasing order by number.
			 */
			Collection<CFGNode> predecessors = reverse ? wInfo.node.getChildren() : wInfo.node.getParents();
			List<CFGNode> preds = predecessors.stream().sorted(
				(CFGNode a, CFGNode b) -> {
					if (infoMap.get(a).dfs < infoMap.get(b).dfs) {
						return 1;
					} else {
						return -1;
					}
				}
			).collect(Collectors.toList());

			System.out.print(wInfo.node + "\n" + "\n    ");
			preds.forEach(s -> System.out.print(infoMap.get(s).dfs + " "));
			System.out.print("\n");

			for (CFGNode pred : preds) {
				NodeInfo vInfo = infoMap.get(pred);
				int u = eval(vInfo, ancestor, vertices);
				NodeInfo uInfo = vertices.get(u);

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
				NodeInfo vInfo = vertices.get(v);
				int u = eval(vInfo, ancestor, vertices);
				NodeInfo uInfo = vertices.get(u);

				vInfo.idom = uInfo.sdom < vInfo.sdom ? u : p;
				iter.remove();
			}
		}

		/*
		 * Step 4: Explicitly define the immediate dominator of each vertex,
		 * carrying out the computation vertex by vertex in increasing order by number
		 */
		for (int w = 2; w <= cnt; ++w) {
			NodeInfo wInfo = vertices.get(w);
			if (wInfo.idom != vertices.get(wInfo.sdom).dfs) {
				wInfo.idom = vertices.get(wInfo.idom).idom;
			}
		}

		infoMap.get(root).idom = 0;

		/* Construct the tree */
		Map<CFGNode, DominatorTreeNode> domMapping = new HashMap<>();
		for (NodeInfo info : infoMap.values()) {
			if (info.dfs == 1)
				continue; // Skip the entry node

			DominatorTreeNode idom = vertices.get(info.idom).domNode;
			info.domNode.setParent(idom);
			domMapping.put(info.node, info.domNode);
		}

		DominatorTreeNode domTreeEntry = infoMap.get(root).domNode;

		return new DominatorTree(domTreeEntry, domMapping);
	}

	private static void link(int v, int w, int[] ancestor)
	{
		ancestor[v] = w;
	}

	private static int eval(NodeInfo vInfo, int[] ancestor, List<NodeInfo> vertices)
	{
		int a = ancestor[vInfo.dfs];
		int v = vInfo.dfs;

		while (a != 0) {
			if (vInfo.sdom > vertices.get(a).sdom) {
				v = a;
			}
			a = ancestor[a];
		}

		return v;
	}

	private static int DFS(CFGNode node, int cnt, Map<CFGNode, NodeInfo> infoMap, List<NodeInfo> vertices, boolean reverse)
	{
		NodeInfo info = infoMap.get(node);
		info.sdom = info.dfs = ++cnt;
		vertices.add(info);

		Collection<CFGNode> children = reverse ? node.getParents() : node.getChildren();

		for (CFGNode child : children) {
			NodeInfo childInfo = infoMap.get(child);
			if (childInfo.sdom == 0) {
				childInfo.parent = info.dfs;
				cnt = DFS(child, cnt, infoMap, vertices, reverse);
			}
		}

		return cnt;
	}

}
