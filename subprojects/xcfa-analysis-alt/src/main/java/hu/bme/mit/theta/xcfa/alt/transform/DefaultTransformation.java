package hu.bme.mit.theta.xcfa.alt.transform;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.EnterWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.ExitWaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyStmt;
import hu.bme.mit.theta.core.stmt.xcfa.WaitStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.algorithm.Config;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Transforms empty edges to edge with skip stmt.
 * Transforms wait edge to two separate stmts.
 * Transforms notify edge to a special construct (see copy(_, Edge))
 * TODO needs robust testing and configuration
 */
public class DefaultTransformation extends EmptyTransformation {

    private final Config config;

    public DefaultTransformation(XCFA old, Config config) {
        super(old);
        this.config = config;
    }

    /**
     * Circular dependency in Builder pattern -> save the stmts
     * Mapped to the old process, so it can be transformed
     */
    Map<InternalNotifyStmt, XCFA.Process> internalNotifyStmts = new HashMap<>();

    /**
     * For every global synthetic variable, creates a spurious wake-up call thread.
     *
     * The matching XCFA:
     * init L0
     * final L1
     *
     * L0 -> L1 { }
     * L0 -> L0 { notify var }
     *
     * for every process A, B, ...
     *
     * The main advantage of this is:
     * 1) spurious wake-up works as expected
     * 2) deadlock is detected like there was no spurious wake-up
     */
    @Override
    protected void beforeBuild(XCFA.Builder builder) {
        // save builder data BEFORE modifying
        if (config.spuriousWakeUp()) {
            var varsBefore = builder.getGlobalVars();
            for (VarDecl<? extends Type> var : varsBefore) {
                if (var.getType() instanceof SyntheticType) {
                    var procedure = XCFA.Process.Procedure.builder();

                    procedure.setName("main");

                    // transformed is needed here for transforming the NotifyStmt
                    XCFA.Process.Procedure.Location l0 = transformed(procedure, new XCFA.Process.Procedure.Location("L0", Map.of()));
                    XCFA.Process.Procedure.Location l1 = transformed(procedure, new XCFA.Process.Procedure.Location("L1", Map.of()));
                    procedure.addLoc(l0);
                    procedure.addLoc(l1);
                    procedure.setInitLoc(l0);
                    procedure.setFinalLoc(l1);

                    var skipEdge = new XCFA.Process.Procedure.Edge(l0, l1, List.of(SkipStmt.getInstance()));
                    procedure.addEdge(transformed(procedure, skipEdge));
                    var notifyEdge = new XCFA.Process.Procedure.Edge(l0, l0, List.of(new NotifyStmt(var)));
                    // we have to process it -> call copy
                    procedure.addEdge(transformed(procedure, notifyEdge));
                    var procedureBuilt = procedure.build();

                    var process = XCFA.Process.builder();
                    process.setName("Spurious_" + var.getName());

                    process.addProcedure(procedureBuilt);
                    process.setMainProcedure(procedureBuilt);

                    builder.addProcess(process.build());
                }
            }
        }
    }

    /**
     * Resolves circular dependency by post-processing (needed because of the Builder pattern).
     */
    @Override
    protected void afterBuild(XCFA xcfa) {
        for (var entry : internalNotifyStmts.entrySet()) {
            var stmt = entry.getKey();
            var oldProcess = entry.getValue();
            // builder is not needed, because the transformed value is already cached
            var process = transformed(null, oldProcess);
            stmt.setProcess(process);
        }
    }

    /**
     * Responsible for empty stmt list and transforming WaitStmt and NotifyStmt
     * Creates skip stmt from empty stmt list
     * Splits WaitStmt into two.
     *
     * EMPTY STMT:
     * LA -> LB { }
     *
     * will become
     *
     * LA -> LB { skip }
     *
     *
     * WAIT:
     * LA -> LB { wait var }
     *
     * will become
     *
     * LA -> LA_midwait { enterWait var }
     * LA_midwait -> LB { exitWait var }
     * (both enterWait and exitWait are internal, and cannot be accessed from XCFA)
     *
     *
     * NOTIFY:
     * Note that notifyAll is does not need special handling. For NOTIFY, however there are many requirements:
     *
     * 1) It is atomic.
     * 2) NOP iff No process waiting
     * 3) notify AT LEAST one waiting process if there is at least one process waiting
     *     All docs about in every implementation (C++, Java) say that there may be more than one thread notified!
     *     Note that notifying a "random" thread does not work, because it might not be waiting.
     *
     * __The first thought:__
     * Create a deterministic^ simple statement that can be used to build the notify statement.
     * InternalNotifyStmt: Remove _a given_ process from wait set if present.
     *     If not present in the wait set, stmt is disabled.
     * ^: this is needed it works with the verifier algorithms.
     *
     * __The second thought:__
     * Make the whole transition atomic.
     * Create two new locations LA_inAtomic and LB_outAtomic
     *     Note that suffix needs to be different for LA -> LB { notify var } LB -> LC { notify var }
     *     There will be an LB_inAtomic and LB_outAtomic too.
     * LA -> LA_in { atomicBegin }
     * LA_in -> LB_out { ??? }
     * LB_out -> LB { atomicEnd }
     *
     * __The third thought:__
     * To fulfill the 2nd requirement, we need a new transition.
     * For simplicity, internalNotify with process of null can be used for this.
     *
     * Putting it together:
     * Create an InternalNotifyStmt with arguments SyntheticVar, Process
     *     With process==null, it could be written as "assume var.waitSet==empty".
     *     With process!=null, it could be written as "assume process in var.waitSet; var.waitSet.remove(process)"
     *         Note that there is no "waitSet" in XCFA.
     *
     * LA -> LB { internal-notify var, null } // handle the case of empty waitSet
     * LA -> LA_in { atomic-begin }
     *
     * LA_in -> LB_out { notify var, process1 }
     * ...
     * LA_in -> LB_out { notify var, processN }
     * LB_out -> LA_in { }
     *
     * LB_out -> LB { atomic-end }
     */
    @Override
    protected XCFA.Process.Procedure.Edge copy(XCFA.Process.Procedure.Builder builder, XCFA.Process.Procedure.Edge edge) {
        if (edge.getStmts().isEmpty()) {
            // create skip stmt
            var source = transformed(builder, edge.getSource());
            var target = transformed(builder, edge.getTarget());
            return new XCFA.Process.Procedure.Edge(
                    source, target, List.of(SkipStmt.getInstance())
            );
        }
        Preconditions.checkArgument(edge.getStmts().size() == 1);
        if (edge.getStmts().get(0) instanceof NotifyStmt) {
            var stmt = (NotifyStmt) edge.getStmts().get(0);
            var var = stmt.getSyncVar();
            var source = transformed(builder, edge.getSource());
            var target = transformed(builder, edge.getTarget());
            var sourceIn = new XCFA.Process.Procedure.Location(source.getName() + "_inNotify", Map.of());
            var targetOut = new XCFA.Process.Procedure.Location(target.getName() + "_outNotify", Map.of());

            var eEmptyWaitSet = new XCFA.Process.Procedure.Edge(source, target,
                    List.of(new InternalNotifyStmt(var, null))
            );

            var eAtomicBegin = new XCFA.Process.Procedure.Edge(source, sourceIn,
                    List.of(new AtomicBeginStmt()));
            var eAtomicEnd = new XCFA.Process.Procedure.Edge(source, sourceIn,
                    List.of(new AtomicEndStmt()));
            var eBackEdge = new XCFA.Process.Procedure.Edge(sourceIn, targetOut,
                    List.of(Stmts.Skip()));

            for (var oldProcess : old.getProcesses()) {
                // circular dependency -> save the stmt for later, and fill process with null
                var internalStmt = new InternalNotifyStmt(var, null);
                internalNotifyStmts.put(internalStmt, oldProcess);
                builder.addEdge(
                        new XCFA.Process.Procedure.Edge(sourceIn, targetOut,
                                List.of(internalStmt))
                );
            }

            builder.addLoc(sourceIn);
            builder.addLoc(targetOut);
            builder.addEdge(eEmptyWaitSet);
            builder.addEdge(eAtomicEnd);
            builder.addEdge(eBackEdge);

            return eAtomicBegin;// builder.addEdge(eAtomicBegin);
        } else if (edge.getStmts().get(0) instanceof WaitStmt) {
            var stmt = (WaitStmt) edge.getStmts().get(0);
            var source = transformed(builder, edge.getSource());
            var target = transformed(builder, edge.getTarget());
            var mid = new XCFA.Process.Procedure.Location(source.getName() + "_midwait",
                    Map.of());
            var e1 = new XCFA.Process.Procedure.Edge(source, mid, List.of(
                    new EnterWaitStmt(stmt.getSyncVar())
            ));
            var e2 = new XCFA.Process.Procedure.Edge(mid, target, List.of(
                    new ExitWaitStmt(stmt.getSyncVar())
            ));

            builder.addLoc(mid);
            builder.addEdge(e2);
            return e1; //builder.addEdge(e1);
        } else {
            return super.copy(builder, edge);
        }
    }
}
