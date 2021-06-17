package hu.bme.mit.theta.xcfa.analysis.weakmemory.bounded;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class ExecutionGraphPrinter {
	static void print(Datalog program) {
		Datalog.Relation po = program.getRelations().get("po");
		Datalog.Relation rf = program.getRelations().get("rf");
		Datalog.Relation r = program.getRelations().get("r");
		Datalog.Relation w = program.getRelations().get("w");
		Datalog.Relation f = program.getRelations().get("f");
//		Datalog.Relation errorLoc = program.getRelations().get("error");
//		Datalog.Relation initLoc = program.getRelations().get("init");
//		Datalog.Relation finalLoc = program.getRelations().get("final");

		System.out.println("digraph G{");

		Set<Tuple2<GenericDatalogArgument<?>, String>> nodeNames = new LinkedHashSet<>();
		int counter = 0;
		for (TupleN<DatalogArgument> element : r.getElements()) {
			String name = "Stmt" + counter++;
			nodeNames.add(Tuple2.of((GenericDatalogArgument<?>) element.get(0), name));
			checkState(element.get(1) instanceof GenericDatalogArgument<?> && ((GenericDatalogArgument<?>) element.get(1)).getContent() instanceof VarDecl<?>);
			System.out.println(name + "[label=\"R(" + ((VarDecl<?>) ((GenericDatalogArgument<?>) element.get(1)).getContent()).getName() + ")\"];");
		}
		for (TupleN<DatalogArgument> element : w.getElements()) {
			String name = "Stmt" + counter++;
			nodeNames.add(Tuple2.of((GenericDatalogArgument<?>) element.get(0), name));
			checkState(element.get(1) instanceof GenericDatalogArgument<?> && ((GenericDatalogArgument<?>) element.get(1)).getContent() instanceof VarDecl<?>);
			System.out.println(name + "[label=\"W(" + ((VarDecl<?>) ((GenericDatalogArgument<?>) element.get(1)).getContent()).getName() + ")\"];");
		}
		for (TupleN<DatalogArgument> element : f.getElements()) {
			String name = "Stmt" + counter++;
			nodeNames.add(Tuple2.of((GenericDatalogArgument<?>) element.get(0), name));
			System.out.println(name + "[label=\"F\"];");
		}
//		for (TupleN<DatalogArgument> element : initLoc.getElements()) {
//			String name = "Stmt" + counter++;
//			nodeNames.put(element.get(0), name);
//			System.out.println(name + "[color=green,label=\"\"];");
//		}
//		for (TupleN<DatalogArgument> element : errorLoc.getElements()) {
//			String name = "Stmt" + counter++;
//			nodeNames.put(element.get(0), name);
//			System.out.println(name + "[color=red,label=\"\"];");
//		}
//		for (TupleN<DatalogArgument> element : finalLoc.getElements()) {
//			String name = "Stmt" + counter++;
//			nodeNames.put(element.get(0), name);
//			System.out.println(name + "[color=black,label=\"\"];");
//		}
		for (TupleN<DatalogArgument> element : po.getElements()) {
			checkState(element.get(0) instanceof GenericDatalogArgument<?>);
			Optional<Tuple2<GenericDatalogArgument<?>, String>> sourceOpt = nodeNames.stream().filter(el -> element.get(0) instanceof GenericDatalogArgument<?> && ((GenericDatalogArgument<?>) element.get(0)).getContent() == el.get1().getContent()).findFirst();
			Optional<Tuple2<GenericDatalogArgument<?>, String>> targetOpt = nodeNames.stream().filter(el -> element.get(1) instanceof GenericDatalogArgument<?> && ((GenericDatalogArgument<?>) element.get(1)).getContent() == el.get1().getContent()).findFirst();
			if(sourceOpt.isEmpty()) sourceOpt = Optional.of(Tuple2.of(GenericDatalogArgument.createArgument(""), "init"));
			checkState(targetOpt.isPresent());
			System.out.println(sourceOpt.get().get2() + "->" + targetOpt.get().get2() + ";");
		}
		for (TupleN<DatalogArgument> element : rf.getElements()) {
			checkState(element.get(0) instanceof GenericDatalogArgument<?>);
			Optional<Tuple2<GenericDatalogArgument<?>, String>> sourceOpt = nodeNames.stream().filter(el -> element.get(0) instanceof GenericDatalogArgument<?> && ((GenericDatalogArgument<?>) element.get(0)).getContent() == el.get1().getContent()).findFirst();
			Optional<Tuple2<GenericDatalogArgument<?>, String>> targetOpt = nodeNames.stream().filter(el -> element.get(1) instanceof GenericDatalogArgument<?> && ((GenericDatalogArgument<?>) element.get(1)).getContent() == el.get1().getContent()).findFirst();
			checkState(sourceOpt.isPresent());
			checkState(targetOpt.isPresent());
			System.out.println(sourceOpt.get().get2() + "->" + targetOpt.get().get2() + "[constraint=false,color=green];");
		}
		System.out.println("}");
	}
}
