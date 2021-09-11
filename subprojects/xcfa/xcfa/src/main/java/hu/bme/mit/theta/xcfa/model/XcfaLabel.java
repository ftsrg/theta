package hu.bme.mit.theta.xcfa.model;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
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
			throw new UnsupportedOperationException("ProcedureCall cannot be transformed into a Stmt!");
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
		}
	}

	public static class StartThreadXcfaLabel extends XcfaLabel {
		private final VarDecl<?> key;
		private final String threadName;
		private final Expr<?> param;

		private StartThreadXcfaLabel(final VarDecl<?> key, final String threadName, final Expr<?> param) {
			this.key = key;
			this.threadName = threadName;
			this.param = param;
		}

		public static StartThreadXcfaLabel of(final VarDecl<?> key, final String threadName, final Expr<?> params) {
			return new StartThreadXcfaLabel(key, threadName, params);
		}

		@Override
		public Stmt getStmt() {
			throw new UnsupportedOperationException("StartThread cannot be transformed into a Stmt!");
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
			throw new UnsupportedOperationException("JoinThread cannot be transformed into a Stmt!");
		}

		public VarDecl<?> getKey() {
			return key;
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
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
			return Assign(local, global.getRef());
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
			return Assign(global, local.getRef());
		}

		@Override
		public <P, R> R accept(XcfaLabelVisitor<P, R> visitor, P param) {
			return visitor.visit(this, param);
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

	public static FenceXcfaLabel Fence(final String type) {
		return FenceXcfaLabel.of(type);
	}

	public static StmtXcfaLabel Stmt(final Stmt stmt) {
		return StmtXcfaLabel.of(stmt);
	}

}
