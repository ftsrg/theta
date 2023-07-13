/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.cat.solver;

public class DatalogSolver {

//    public static void solve(final Datalog mcm, final XCFA xcfa) {
//        final Map<String, Datalog.Relation> relations = mcm.getRelations();
//        final Datalog.Relation po = relations.get("po");
//        final Datalog.Relation r = relations.get("R");
//        final Datalog.Relation w = relations.get("W");
//        final Datalog.Relation f = relations.get("F");
//        for (final XcfaProcess process : xcfa.getProcesses()) {
//            XcfaLocation lastLoc = process.getMainProcedure().getInitLoc();
//            while(!lastLoc.isEndLoc()) {
//                if(lastLoc.getOutgoingEdges().size() != 1) throw new UnsupportedOperationException("Only branchless programs are supported for now");
//                final XcfaEdge xcfaEdge = lastLoc.getOutgoingEdges().get(0);
//                if(xcfaEdge.getLabels().size() != 1)  throw new UnsupportedOperationException("Only single-label edges are supported for now");
//                final XcfaLabel xcfaLabel = xcfaEdge.getLabels().get(0);
//
//                if(xcfaLabel instanceof XcfaLabel.StoreXcfaLabel) w.addFact(TupleN.of(GenericDatalogArgument.createArgument(xcfaEdge.getTarget())));
//                else if(xcfaLabel instanceof XcfaLabel.LoadXcfaLabel) r.addFact(TupleN.of(GenericDatalogArgument.createArgument(xcfaEdge.getTarget())));
//                else if(xcfaLabel instanceof XcfaLabel.FenceXcfaLabel) f.addFact(TupleN.of(GenericDatalogArgument.createArgument(xcfaEdge.getTarget())));
//
//                if(lastLoc != process.getMainProcedure().getInitLoc()) po.addFact(TupleN.of(GenericDatalogArgument.createArgument(lastLoc), GenericDatalogArgument.createArgument(xcfaEdge.getTarget())));
//
//                lastLoc = xcfaEdge.getTarget();
//            }
//        }
//
//        final Object[] writes = w.getElements().stream().map(objects -> ((GenericDatalogArgument<?>)objects.get(0)).getContent()).toArray();
//        final Object[] reads = r.getElements().stream().map(objects -> ((GenericDatalogArgument<?>)objects.get(0)).getContent()).toArray();
//        generateCos(writes, mcm, null, () -> generateRfs(reads, writes, mcm, () -> {
//            System.out.println("digraph G{");
//            final Datalog.Relation rf = mcm.getRelations().get("rf");
//            for (TupleN<DatalogArgument> element : po.getElements()) {
//                System.out.println(element.get(0) + " -> " + element.get(1) + " [color=grey]");
//            }
//            for (TupleN<DatalogArgument> element : rf.getElements()) {
//                System.out.println(element.get(0) + " -> " + element.get(1) + " [color=red]");
//            }
//            System.out.println("}");
//            System.out.println();
//        }));
//    }
//
//    private static void generateRfs(final Object[] reads, final Object[] writes, final Datalog mcm, final Runnable whenComplete) {
//        if(reads.length > 0) {
//            final Object read = reads[0];
//            for (Object write : writes) {
//                mcm.push();
//                mcm.getRelations().get("rf").addFact(TupleN.of(GenericDatalogArgument.createArgument(write), GenericDatalogArgument.createArgument(read)));
//                if (mcm.getRelations().get("mustBeEmpty").getElements().size() == 0) {
//                    generateRfs(removeOne(reads, 0), writes, mcm, whenComplete);
//                }
//                mcm.pop();
//            }
//        } else {
//            whenComplete.run();
//        }
//    }
//
//    private static void generateCos(final Object[] writes, final Datalog mcm, final Object last, final Runnable whenComplete) {
//        if(writes.length == 0) {
//            whenComplete.run();
//        } else {
//            for (int i = 0; i < writes.length; i++) {
//                mcm.push();
//                if (last != null)
//                    mcm.getRelations().get("co").addFact(TupleN.of(GenericDatalogArgument.createArgument(last), GenericDatalogArgument.createArgument(writes[i])));
//                if (mcm.getRelations().get("mustBeEmpty").getElements().size() == 0) {
//                    generateCos(removeOne(writes, i), mcm, writes[i], whenComplete);
//                }
//                mcm.pop();
//            }
//        }
//    }
//
//    private static Object[] removeOne(final Object[] input, final int at) {
//        final Object[] ret = new Object[input.length - 1];
//        int idx = 0;
//        for (int i = 0; i < input.length; i++) {
//            if(i != at) {
//                ret[idx++] = input[i];
//            }
//        }
//        return ret;
//    }

}
