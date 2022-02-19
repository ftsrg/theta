package hu.bme.mit.theta.xcfa.model;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.Skip;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public abstract class XcfaLabel {

	public abstract Stmt getStmt();

	public abstract <P, R> R accept(final XcfaLabelVisitor<P, R> visitor, P param);

	public static class AtomicBeginXcfaLabel extends XcfaLabel {
		private final static AtomicBeginXcfaLabel INSTANCE = new AtomicBeginXcfaLabel();

		public static AtomicBeginXcfaLabel getInstance() {
			return INSTANCE;
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("AtomicBegin").toString();
		}
	}

	public static class AtomicEndXcfaLabel extends XcfaLabel {
		private final static AtomicEndXcfaLabel INSTANCE = new AtomicEndXcfaLabel();

		public static AtomicEndXcfaLabel getInstance() {
			return INSTANCE;
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("AtomicEnd").toString();
		}
	}

	public static class ProcedureCallXcfaLabel extends XcfaLabel {
		private final List<Expr<?>> params;
		private final String procedure;

		private ProcedureCallXcfaLabel(final List<Expr<?>> params, final String procedure) {
			this.params = params;
			this.procedure = procedure;
		}

		public static ProcedureCallXcfaLabel of(final List<Expr<?>> params, final String procedure) {
			return new ProcedureCallXcfaLabel(params, procedure);
		}

		public List<Expr<?>> getParams() {
			return params;
		}

		public String getProcedure() {
			return procedure;
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("Call").add(procedure).addAll(params).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			ProcedureCallXcfaLabel that = (ProcedureCallXcfaLabel) o;
			return Objects.equals(params, that.params) && Objects.equals(procedure, that.procedure);
		}

		@Override
		public int hashCode() {
			return Objects.hash(params, procedure);
		}
	}

	public static class StartThreadXcfaLabel extends XcfaLabel {
		private final VarDecl<?> key;
		private final String threadName;
		private Optional<XcfaProcess> process;
		private final Expr<?> param;

		private StartThreadXcfaLabel(final VarDecl<?> key, final String threadName, final Expr<?> param) {
			this.key = key;
			this.threadName = threadName;
			this.param = param;
			this.process = Optional.empty();
		}

		public static StartThreadXcfaLabel of(final VarDecl<?> key, final String threadName, final Expr<?> params) {
			return new StartThreadXcfaLabel(key, threadName, params);
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		public Expr<?> getParam() {
			return param;
		}

		public String getThreadName() {
			return threadName;
		}

		public VarDecl<?> getKey() {
			return key;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		public void setProcedure(final XcfaProcedure startProc) {
			final XcfaProcess process = startProc.getParent().withMainProcedure(startProc);
			this.process = Optional.of(process);
		}

		public XcfaProcess getProcess() {
			checkState(process.isPresent(), "Process was not substituted before usage!");
			return process.get();
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("Start").add(key).add(threadName).add(param).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			StartThreadXcfaLabel that = (StartThreadXcfaLabel) o;
			return key.equals(that.key) && threadName.equals(that.threadName) && param.equals(that.param);
		}

		@Override
		public int hashCode() {
			return Objects.hash(key, threadName, param);
		}
	}

	public static class JoinThreadXcfaLabel extends XcfaLabel {
		private final VarDecl<?> key;

		private JoinThreadXcfaLabel(final VarDecl<?> key) {
			this.key = key;
		}

		public static JoinThreadXcfaLabel of(final VarDecl<?> key) {
			return new JoinThreadXcfaLabel(key);
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		public VarDecl<?> getKey() {
			return key;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("Join").add(key).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			JoinThreadXcfaLabel that = (JoinThreadXcfaLabel) o;
			return key.equals(that.key);
		}

		@Override
		public int hashCode() {
			return Objects.hash(key);
		}
	}

	public static class LoadXcfaLabel<T extends Type> extends XcfaLabel {
		private final VarDecl<T> global;
		private final VarDecl<T> local;
		private final boolean atomic;
		private final String ordering;

		private LoadXcfaLabel(final VarDecl<T> global, final VarDecl<T> local, final boolean atomic, final String ordering) {
			this.global = global;
			this.local = local;
			this.atomic = atomic;
			this.ordering = ordering;
		}

		public static <T extends Type> LoadXcfaLabel<T> of(final VarDecl<T> global, final VarDecl<T> local, final boolean atomic, final String ordering) {
			return new LoadXcfaLabel<T>(global, local, atomic, ordering);
		}

		@Override
		public Stmt getStmt() {
			return Havoc(local);
		}

		public boolean isAtomic() {
			return atomic;
		}

		public String getOrdering() {
			return ordering;
		}

		public VarDecl<T> getGlobal() {
			return global;
		}

		public VarDecl<T> getLocal() {
			return local;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("Load").add(local).add(global).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			LoadXcfaLabel<?> that = (LoadXcfaLabel<?>) o;
			return atomic == that.atomic && global.equals(that.global) && local.equals(that.local) && Objects.equals(ordering, that.ordering);
		}

		@Override
		public int hashCode() {
			return Objects.hash(global, local, atomic, ordering);
		}
	}

	public static class StoreXcfaLabel<T extends Type> extends XcfaLabel {
		private final VarDecl<T> local;
		private final VarDecl<T> global;
		private final boolean atomic;
		private final String ordering;

		private StoreXcfaLabel(final VarDecl<T> local, final VarDecl<T> global, final boolean atomic, final String ordering) {
			this.local = local;
			this.global = global;
			this.atomic = atomic;
			this.ordering = ordering;
		}

		public static <T extends Type> StoreXcfaLabel<T> of(final VarDecl<T> local, final VarDecl<T> global, final boolean atomic, final String ordering) {
			return new StoreXcfaLabel<T>(local, global, atomic, ordering);
		}

		public VarDecl<?> getLocal() {
			return local;
		}

		public VarDecl<?> getGlobal() {
			return global;
		}

		public boolean isAtomic() {
			return atomic;
		}

		public String getOrdering() {
			return ordering;
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("Store").add(global).add(local).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			StoreXcfaLabel<?> that = (StoreXcfaLabel<?>) o;
			return atomic == that.atomic && local.equals(that.local) && global.equals(that.global) && Objects.equals(ordering, that.ordering);
		}

		@Override
		public int hashCode() {
			return Objects.hash(local, global, atomic, ordering);
		}
	}

	public static class FenceXcfaLabel extends XcfaLabel {
		private final String type;

		private FenceXcfaLabel(final String type) {
			this.type = type;
		}

		public static FenceXcfaLabel of(final String type) {
			return new FenceXcfaLabel(type);
		}

		@Override
		public Stmt getStmt() {
			return Skip();
		}

		public String getType() {
			return type;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}


		@Override
		public String toString() {
			return Utils.lispStringBuilder("Fence").add(type).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			FenceXcfaLabel that = (FenceXcfaLabel) o;
			return Objects.equals(type, that.type);
		}

		@Override
		public int hashCode() {
			return Objects.hash(type);
		}
	}

	public static class SequenceLabel extends XcfaLabel {
		private final List<XcfaLabel> labels;

		private SequenceLabel(List<XcfaLabel> labels) {
			this.labels = List.copyOf(labels);
		}

		public static SequenceLabel of(List<XcfaLabel> labels) {
			return new SequenceLabel(labels);
		}

		@Override
		public Stmt getStmt() {
			return SequenceStmt.of(labels.stream().map(label -> label.getStmt()).collect(Collectors.toList()));
		}

		public List<XcfaLabel> getLabels() {
			return labels;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		public String toString() {
			return Utils.lispStringBuilder("Sequence").addAll(labels).toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			SequenceLabel that = (SequenceLabel) o;
			return labels.equals(that.labels);
		}

		@Override
		public int hashCode() {
			return Objects.hash(labels);
		}
	}

	public static class NondetLabel extends XcfaLabel {
		private final List<XcfaLabel> labels;

		private NondetLabel(List<XcfaLabel> labels) {
			this.labels = List.copyOf(labels);
		}

		public static NondetLabel of(List<XcfaLabel> labels) {
			return new NondetLabel(labels);
		}

		@Override
		public Stmt getStmt() {
			return NonDetStmt.of(labels.stream().map(label -> label.getStmt()).collect(Collectors.toList()));
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		public String toString() {
			return Utils.lispStringBuilder("Nondet").addAll(labels).toString();
		}

		public List<XcfaLabel> getLabels() {
			return labels;
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			NondetLabel that = (NondetLabel) o;
			return labels.equals(that.labels);
		}

		@Override
		public int hashCode() {
			return Objects.hash(labels);
		}
	}

	public static class StmtXcfaLabel extends XcfaLabel {
		private final Stmt stmt;

		private StmtXcfaLabel(final Stmt stmt) {
			this.stmt = stmt;
		}

		public static StmtXcfaLabel of(final Stmt stmt) {
			return new StmtXcfaLabel(stmt);
		}

		@Override
		public Stmt getStmt() {
			return stmt;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}

		@Override
		public String toString() {
			return stmt.toString();
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			StmtXcfaLabel that = (StmtXcfaLabel) o;
			return stmt.equals(that.stmt);
		}

		@Override
		public int hashCode() {
			return Objects.hash(stmt);
		}
	}

	public static AtomicBeginXcfaLabel AtomicBegin() {
		return AtomicBeginXcfaLabel.getInstance();
	}

	public static AtomicEndXcfaLabel AtomicEnd() {
		return AtomicEndXcfaLabel.getInstance();
	}

	public static ProcedureCallXcfaLabel ProcedureCall(final List<Expr<?>> params, final String key) {
		return ProcedureCallXcfaLabel.of(params, key);
	}

	public static StartThreadXcfaLabel StartThread(final VarDecl<?> handle, final String key, final Expr<?> param) {
		return StartThreadXcfaLabel.of(handle, key, param);
	}

	public static JoinThreadXcfaLabel JoinThread(final VarDecl<?> handle) {
		return JoinThreadXcfaLabel.of(handle);
	}

	public static <T extends Type, R extends Type> LoadXcfaLabel<T> Load(final VarDecl<T> global, final VarDecl<R> local, final boolean atomic, final String ordering) {
		TypeUtils.checkAllTypesEqual(global.getRef(), local.getRef());
		final VarDecl<T> localT = cast(local, global.getType());
		return LoadXcfaLabel.of(global, localT, atomic, ordering);
	}

	public static <T extends Type, R extends Type> StoreXcfaLabel<T> Store(final VarDecl<T> global, final VarDecl<R> local, final boolean atomic, final String ordering) {
		TypeUtils.checkAllTypesEqual(global.getRef(), local.getRef());
		final VarDecl<T> localT = cast(local, global.getType());
		return StoreXcfaLabel.of(global, localT, atomic, ordering);
	}

	public static SequenceLabel Sequence(final List<XcfaLabel> labels) { return XcfaLabel.SequenceLabel.of(labels); }

	public static NondetLabel Nondet(final List<XcfaLabel> labels) { return XcfaLabel.NondetLabel.of(labels); }

	public static FenceXcfaLabel Fence(final String type) {
		return FenceXcfaLabel.of(type);
	}

	public static StmtXcfaLabel Stmt(final Stmt stmt) {
		return StmtXcfaLabel.of(stmt);
	}

}
