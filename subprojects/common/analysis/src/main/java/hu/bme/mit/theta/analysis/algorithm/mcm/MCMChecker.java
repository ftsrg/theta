/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.mcm.cegar.AbstractExecutionGraph;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEvent.MemoryEventType.*;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;

public class MCMChecker<S extends ExprState, A extends StmtAction, P extends Prec> {
    private final MemoryEventProvider<S, A> memoryEventProvider;
    private final MultiprocLTS<S, A> multiprocLTS;
    private final MultiprocInitFunc<S, P> multiprocInitFunc;
    private final MultiprocTransFunc<S, A, P> multiprocTransFunc;
    private final Collection<Integer> pids;
    private final Collection<MemoryEvent.Write> initialWrites;
    private final PartialOrd<S> partialOrd;
    private final ExprState globalInitState;
    private final Solver solver;
    private final MCM mcm;
    private final Logger logger;

    public MCMChecker(
            final MemoryEventProvider<S, A> memoryEventProvider,
            final MultiprocLTS<S, A> multiprocLTS,
            final MultiprocInitFunc<S, P> multiprocInitFunc,
            final MultiprocTransFunc<S, A, P> multiprocTransFunc,
            final Collection<Integer> pids,
            final Collection<MemoryEvent.Write> initialWrites,
            final PartialOrd<S> partialOrd,
            final ExprState globalInitState,
            final Solver solver,
            final MCM mcm,
            final Logger logger) {
        this.initialWrites = initialWrites;
        this.partialOrd = partialOrd;
        this.globalInitState = globalInitState;
        checkArgument(pids.stream().noneMatch(i -> i >= 0), "Meta event IDs must be negative!");

        this.memoryEventProvider = memoryEventProvider;
        this.multiprocLTS = multiprocLTS;
        this.multiprocInitFunc = multiprocInitFunc;
        this.multiprocTransFunc = multiprocTransFunc;
        this.pids = pids;
        this.solver = solver;
        this.mcm = mcm;
        this.logger = logger;
    }

    public MCMSafetyResult check(final P prec) {
        logger.write(Logger.Level.MAINSTEP, "Starting verification\n");
        logger.write(Logger.Level.INFO, "Current precision: " + prec + "\n");
        final Collection<VarDecl<?>> usedVars = prec.getUsedVars();
        logger.write(Logger.Level.INFO, "Variables in precision: " + usedVars + "\n");
        final AbstractExecutionGraph<S, A> executionGraph = new AbstractExecutionGraph<S, A>(List.of("RX", "A", "DMB.SY", "thread-end", "meta"), solver, this.mcm, partialOrd);

        final List<Integer> initialWriteEvents = new ArrayList<>();

        final List<List<Integer>> events = new ArrayList<>();
        final Map<Integer, String> eventVarLookup = new LinkedHashMap<>();
        final Collection<DelayedEvent> delayedEvents = new LinkedHashSet<>();
        final Map<Integer, Collection<DelayedRead>> delayedReads = new LinkedHashMap<>();
        final Map<Integer, Collection<Tuple2<Integer, Expr<BoolType>>>> writes = new LinkedHashMap<>();

        for (MemoryEvent.Write initialWrite : initialWrites) {
            int i = executionGraph.addInitialWrite(initialWrite.varId(), Set.of());
            initialWriteEvents.add(i);
            writes.putIfAbsent(initialWrite.varId(), new LinkedHashSet<>());
            writes.get(initialWrite.varId()).add(Tuple2.of(i, globalInitState.toExpr()));
            eventVarLookup.put(i, initialWrite.var().getName());
        }
        logger.write(Logger.Level.SUBSTEP, "|-- Added initial writes: " + initialWriteEvents.size() + "\n");


        final Map<Integer, Map<MemoryEvent.Read, Integer>> readsMap = new LinkedHashMap<>();
        final Map<Integer, List<Integer>> eventListMap = new LinkedHashMap<>();


        for (final int pid : pids) {
            logger.write(Logger.Level.SUBSTEP, "|-- Starting exploration of pid " + pid + "\n");
            final Map<MemoryEvent.Read, Integer> reads = new LinkedHashMap<>();
            readsMap.put(pid, reads);
            final List<Integer> eventList = new ArrayList<>();
            eventListMap.put(pid, eventList);
            events.add(eventList);

            final Collection<? extends S> initStates = multiprocInitFunc.getInitStates(pid, prec);

            for (final S initState : initStates) {
                int id = executionGraph.addInitialState(pid, initState, false);
                logger.write(Logger.Level.SUBSTEP, "|------ Adding init state #" + id + "(pid #" + pid + ")\n");
                delayedEvents.add(new DelayedEvent(pid, id, initState));
            }
        }


        while (true) {
            Optional<DelayedEvent> delayedEvent = delayedEvents.stream().findAny();
            if (delayedEvent.isEmpty()) break;
            delayedEvents.remove(delayedEvent.get());

            final int lastId = delayedEvent.get().getId();
            final S state = delayedEvent.get().getS();
            final int pid = delayedEvent.get().getPid();
            final Map<MemoryEvent.Read, Integer> reads = readsMap.get(pid);
            final List<Integer> eventList = eventListMap.get(pid);

            if (delayedEvent.get() instanceof final DelayedRead delayedRead) {
                handleDelayedRead(prec, usedVars, executionGraph, delayedEvents, delayedReads, writes, lastId, state, pid, reads, eventList, delayedRead, eventVarLookup);
            } else {
                handleEvent(prec, usedVars, executionGraph, delayedEvents, delayedReads, writes, lastId, state, pid, reads, eventList, eventVarLookup);
            }
        }

        final Collection<Map<Decl<?>, LitExpr<?>>> solutions = new ArrayList<>();
        EventConstantLookup rf = executionGraph.encode();

        logger.write(Logger.Level.SUBSTEP, "|-- Successfully built execution graph\n");
        while (executionGraph.nextSolution(solutions)) {
            logger.write(Logger.Level.SUBSTEP, "|-- Found new solution: " + executionGraph.getRf() + "\n");
        }

        logger.write(Logger.Level.RESULT, "Number of executions: " + solutions.size() + "\n");
        logger.write(Logger.Level.MAINSTEP, "Verification ended\n");
        return new MCMSafetyResult(solutions, events, initialWriteEvents, eventVarLookup);
    }

    private void handleEvent(P prec, Collection<VarDecl<?>> usedVars, AbstractExecutionGraph<S, A> executionGraph, Collection<DelayedEvent> delayedEvents, Map<Integer, Collection<DelayedRead>> delayedReads, Map<Integer, Collection<Tuple2<Integer, Expr<BoolType>>>> writes, int lastId, S state, int pid, Map<MemoryEvent.Read, Integer> reads, List<Integer> eventList, Map<Integer, String> eventVarLookup) {
        final Collection<A> enabledActionsFor = multiprocLTS.getEnabledActionsFor(pid, state);
        for (final A a : enabledActionsFor) {
            final List<MemoryEventProvider.ResultElement<A>> piecesOf = List.copyOf(memoryEventProvider.getPiecewiseAction(state, a));
            Collection<DelayedEvent> states = new ArrayList<>(List.of(new DelayedEvent(pid, lastId, state)));
            Collection<DelayedEvent> nextStates = new ArrayList<>();

            for (int i = 0; i < piecesOf.size(); i++) {
                MemoryEventProvider.ResultElement<A> piece = piecesOf.get(i);
                if (exploreActionPiece(prec, usedVars, executionGraph, delayedEvents, delayedReads, writes, pid, reads, eventList, a, states, nextStates, i, piece, i == piecesOf.size() - 1, eventVarLookup)) {
                    states = nextStates;
                    break;
                }
                states = nextStates;
                nextStates = new ArrayList<>();
            }
            for (DelayedEvent delayedEvent : states) {
                if (!executionGraph.tryCover(delayedEvent.getPid(), delayedEvent.getId())) {
                    delayedEvents.add(delayedEvent);
                }
            }
        }
    }

    private void handleDelayedRead(P prec, Collection<VarDecl<?>> usedVars, AbstractExecutionGraph<S, A> executionGraph, Collection<DelayedEvent> delayedEvents, Map<Integer, Collection<DelayedRead>> delayedReads, Map<Integer, Collection<Tuple2<Integer, Expr<BoolType>>>> writes, int lastId, S state, int pid, Map<MemoryEvent.Read, Integer> reads, List<Integer> eventList, DelayedRead delayedRead, Map<Integer, String> eventVarLookup) {
        final A a = delayedRead.getA();
        final int pieceNo = delayedRead.getPieceNo();

        final List<MemoryEventProvider.ResultElement<A>> piecesOf = List.copyOf(memoryEventProvider.getPiecewiseAction(state, a));
        final MemoryEventProvider.ResultElement<A> read = piecesOf.get(pieceNo);
        checkState(read.isMemoryEvent() && read.getMemoryEvent().type() == READ, "Delayed read should actually be a read!");

        int id = executionGraph.addMustRf(pid, delayedRead.getId(), memoryEventProvider.createAction(state, List.of()), state, delayedRead.getReadsFrom());
        eventList.add(id);
        logger.write(Logger.Level.INFO, "|------ Adding rf " + delayedRead.getReadsFrom() + " -> " + delayedRead.getId() + "\n");

        Collection<DelayedEvent> states = new ArrayList<>(List.of(new DelayedEvent(pid, id, state)));
        Collection<DelayedEvent> nextStates = new ArrayList<>();
        for (int i = pieceNo + 1; i < piecesOf.size(); i++) {
            MemoryEventProvider.ResultElement<A> piece = piecesOf.get(i);
            if (exploreActionPiece(prec, usedVars, executionGraph, delayedEvents, delayedReads, writes, pid, reads, eventList, a, states, nextStates, i, piece, i == piecesOf.size() - 1, eventVarLookup)) {
                states = nextStates;
                break;
            }
            states = nextStates;
            nextStates = new ArrayList<>();
        }
        for (DelayedEvent delayedEvent : states) {
            if (!executionGraph.tryCover(delayedEvent.getPid(), delayedEvent.getId())) {
                delayedEvents.add(delayedEvent);
            }
        }
    }

    private boolean exploreActionPiece(P prec, Collection<VarDecl<?>> usedVars, AbstractExecutionGraph<S, A> executionGraph, Collection<DelayedEvent> delayedEvents, Map<Integer, Collection<DelayedRead>> delayedReads, Map<Integer, Collection<Tuple2<Integer, Expr<BoolType>>>> writes, int pid, Map<MemoryEvent.Read, Integer> reads, List<Integer> eventList, A a, Collection<DelayedEvent> states, Collection<DelayedEvent> nextStates, int i, MemoryEventProvider.ResultElement<A> piece, boolean isLastPiece, Map<Integer, String> eventVarLookup) {
        for (DelayedEvent s : states) {
            if (piece.isMemoryEvent()) {
                MemoryEvent memoryEvent = piece.getMemoryEvent();
                int nextId = executionGraph.addMemoryEvent(memoryEvent, pid, s.getId());
                logger.write(Logger.Level.SUBSTEP, "|------ Adding memory event #" + nextId + ": " + piece + "\n");

                if (memoryEvent.type == READ || memoryEvent.type == WRITE) {
                    MemoryEvent.MemoryIO memoryIO = memoryEvent.asMemoryIO();
                    eventVarLookup.put(nextId, memoryIO.var().getName());
                }

                if (memoryEvent.type() == READ) reads.put(memoryEvent.asRead(), nextId);
                else if (memoryEvent.type() == WRITE) {
                    writes.putIfAbsent(memoryEvent.asWrite().varId(), new LinkedHashSet<>());
                    writes.get(memoryEvent.asWrite().varId()).add(Tuple2.of(nextId, s.getS().toExpr()));
                    for (MemoryEvent.Read read : reads.keySet()) {
                        if (memoryEvent.asWrite().dependencies().contains(read.localVar())) {
                            executionGraph.addDataDependency(reads.get(read), nextId);
                        }
                    }

                    for (final DelayedRead delayedRead : delayedReads.getOrDefault(memoryEvent.asWrite().varId(), List.of())) {
                        for (S succState : multiprocTransFunc.getSuccStates(pid, delayedRead.getS(), memoryEventProvider.createAction(delayedRead.getS(), List.of(Assume(s.getS().toExpr()))), prec)) {
                            delayedEvents.add(delayedRead.withS(succState).withRf(nextId));
                        }
                    }
                }
                eventList.add(nextId);

                if (memoryEvent.type() == READ && usedVars.contains(memoryEvent.asRead().var())) {
                    delayedReads.putIfAbsent(memoryEvent.asRead().varId(), new LinkedHashSet<>());
                    DelayedRead delayedRead = new DelayedRead(pid, nextId, a, i, s.getS(), -1);
                    delayedReads.get(memoryEvent.asRead().varId()).add(delayedRead);
                    logger.write(Logger.Level.SUBSTEP, "|------ Delaying read #" + nextId + ": " + piece + "\n");

                    for (final Tuple2<Integer, Expr<BoolType>> write : writes.getOrDefault(memoryEvent.asRead().varId(), List.of())) {
                        for (S succState : multiprocTransFunc.getSuccStates(pid, s.getS(), memoryEventProvider.createAction(s.getS(), List.of(Assume(write.get2()))), prec)) {
                            delayedEvents.add(delayedRead.withS(succState).withRf(write.get1()));
                        }
                    }
                    return true;
                } else {
                    nextStates.add(new DelayedEvent(pid, nextId, s.getS()));
                }
            } else {
                final Collection<? extends S> succStates = multiprocTransFunc.getSuccStates(pid, s.getS(), piece.getAction(), prec);
                for (final S succState : succStates) {
                    int id = executionGraph.addState(s.getId(), pid, piece.getAction(), succState, false, isLastPiece);
                    logger.write(Logger.Level.SUBSTEP, "|------ Adding action #" + id + ": " + piece.getAction() + "\n");
                    nextStates.add(new DelayedEvent(pid, id, succState));
                }
            }
        }
        return false;
    }

    private class DelayedEvent {
        protected final int pid;
        protected final int id;
        protected final S s;

        public DelayedEvent(int pid, int id, S state) {
            this.pid = pid;
            this.id = id;
            this.s = state;
        }

        public int getPid() {
            return pid;
        }

        public int getId() {
            return id;
        }

        public S getS() {
            return s;
        }
    }

    private class DelayedRead extends DelayedEvent {
        private final A a;
        private final int pieceNo;
        private final int readsFrom;

        private DelayedRead(int pid, int id, A a, int pieceNo, S s, int readsFrom) {
            super(pid, id, s);
            this.a = a;
            this.pieceNo = pieceNo;
            this.readsFrom = readsFrom;
        }

        public A getA() {
            return a;
        }

        public int getPieceNo() {
            return pieceNo;
        }

        public int getReadsFrom() {
            return readsFrom;
        }

        public DelayedRead withS(final S s) {
            return new DelayedRead(pid, id, a, pieceNo, s, readsFrom);
        }

        public DelayedEvent withRf(int write) {
            return new DelayedRead(pid, id, a, pieceNo, s, write);
        }
    }

    public static class MCMSafetyResult {
        private final Collection<Map<Decl<?>, LitExpr<?>>> solutions;
        private final List<List<Integer>> events;
        private final List<Integer> initialWriteEvents;
        private final Map<Integer, String> eventVarLookup;

        public MCMSafetyResult(Collection<Map<Decl<?>, LitExpr<?>>> solutions, List<List<Integer>> events, List<Integer> initialWriteEvents, Map<Integer, String> eventVarLookup) {
            this.solutions = solutions;
            this.events = events;
            this.initialWriteEvents = initialWriteEvents;
            this.eventVarLookup = eventVarLookup;
        }

        public Collection<Map<Decl<?>, LitExpr<?>>> getSolutions() {
            return solutions;
        }

        public List<List<Integer>> getEvents() {
            return events;
        }

        public List<Integer> getInitialWriteEvents() {
            return initialWriteEvents;
        }

        public void visualize() {
            new Thread(new ExecutionGraphVisualizer(solutions, events, eventVarLookup, initialWriteEvents)).start();
        }
    }
}
