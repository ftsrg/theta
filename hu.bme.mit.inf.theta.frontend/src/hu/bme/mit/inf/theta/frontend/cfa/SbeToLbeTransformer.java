package hu.bme.mit.inf.theta.frontend.cfa;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.inf.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.inf.theta.formalism.cfa.impl.MutableCfa;

public class SbeToLbeTransformer {

	public static CFA transform(CFA cfa) {
		List<CfaLoc> locs = cfa.getLocs().stream()
			.filter(l -> l != cfa.getInitLoc() && l != cfa.getErrorLoc() && l != cfa.getFinalLoc()) // this also filters out init, error and final
			.collect(Collectors.toList());
		MutableCfa res = new MutableCfa();

		Map<CfaLoc, CfaLoc> mapping = new HashMap<>();
		mapping.put(cfa.getInitLoc(), res.getInitLoc());
		mapping.put(cfa.getErrorLoc(), res.getErrorLoc());
		mapping.put(cfa.getFinalLoc(), res.getFinalLoc());

		for (CfaLoc loc : locs) {
			CfaLoc newLoc = res.createLoc();
			mapping.put(loc, newLoc);
		}

		for (Entry<CfaLoc, CfaLoc> entry : mapping.entrySet()) {
			for (CfaEdge out : entry.getKey().getOutEdges()) {
				CfaLoc dst = mapping.get(out.getTarget());
				CfaEdge edge = res.createEdge(entry.getValue(), dst);
				edge.getStmts().addAll(out.getStmts());
			}
		}

		boolean change = true;
		while (change) {
			change = false;

			Optional<CfaLoc> find = res.getLocs().stream()
				.filter(l -> l != cfa.getInitLoc() && l != cfa.getErrorLoc() && l != cfa.getFinalLoc())
				.filter(l -> l.getInEdges().size() == 1 && l.getOutEdges().size() == 1)
				.findFirst();

			if (find.isPresent()) {
				CfaLoc loc = find.get();
				CfaEdge inEdge = loc.getInEdges().iterator().next();
				CfaEdge outEdge = loc.getOutEdges().iterator().next();

				CfaLoc parent = inEdge.getSource();
				CfaLoc child = outEdge.getTarget();

				CfaEdge newEdge = res.createEdge(parent, child);
				newEdge.getStmts().addAll(inEdge.getStmts());
				newEdge.getStmts().addAll(outEdge.getStmts());

				res.removeEdge(outEdge);
				res.removeEdge(inEdge);

				res.removeLoc(loc);

				change = true;
			}
		}

		return res;
	}

}
