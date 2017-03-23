package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc.Kind;

public final class XtaProcess {
	private final String name;
	private final Collection<VarDecl<?>> vars;
	private final Collection<Loc> locs;
	private final Collection<Edge> edges;
	private Loc initLoc;

	private final Collection<VarDecl<?>> unmodVars;
	private final Collection<Loc> unmodLocs;
	private final Collection<Edge> unmodEdges;

	////

	private XtaProcess(final String name) {
		this.name = checkNotNull(name);
		vars = new HashSet<>();
		locs = new HashSet<>();
		edges = new ArrayList<>();

		unmodVars = Collections.unmodifiableCollection(vars);
		unmodLocs = Collections.unmodifiableCollection(locs);
		unmodEdges = Collections.unmodifiableCollection(edges);
	}

	public static XtaProcess create(final String name) {
		return new XtaProcess(name);
	}

	////

	public String getName() {
		return name;
	}

	public Collection<VarDecl<?>> getVars() {
		return unmodVars;
	}

	public Collection<Loc> getLocs() {
		return unmodLocs;
	}

	public Collection<Edge> getEdges() {
		return unmodEdges;
	}

	public Loc getInitLoc() {
		checkNotNull(initLoc);
		return initLoc;
	}

	////

	public void setInitLoc(final Loc loc) {
		checkNotNull(loc);
		checkArgument(locs.contains(loc));
		this.initLoc = loc;
	}

	public Loc createLoc(final String name, final Kind kind, final Collection<Expr<BoolType>> invars) {
		final Loc loc = new Loc(name, kind, invars);
		locs.add(loc);
		vars.addAll(extractVarsFromLoc(loc));
		return loc;
	}

	public Edge createEdge(final Loc source, final Loc target, final Collection<Expr<BoolType>> guards,
			final Optional<SyncLabel> sync, final List<AssignStmt<?, ?>> updates) {
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));
		final Edge edge = new Edge(source, target, guards, sync, updates);
		vars.addAll(extractVarsFromEdge(edge));
		source.outEdges.add(edge);
		target.inEdges.add(edge);
		return edge;
	}

	////

	private static Collection<VarDecl<?>> extractVarsFromExpr(final Expr<?> expr) {
		return ExprUtils.getVars(expr);
	}

	private static Collection<VarDecl<?>> extractVarsFromExprs(final Collection<? extends Expr<?>> exprs) {
		return ExprUtils.getVars(exprs);
	}

	private static Collection<VarDecl<?>> extractVarsFromStmts(final Collection<? extends Stmt> stmts) {
		return StmtUtils.getVars(stmts);
	}

	private static Collection<VarDecl<?>> extractVarsFromLoc(final Loc loc) {
		return extractVarsFromExprs(loc.invars);
	}

	private static Collection<VarDecl<?>> extractVarsFromEdge(final Edge edge) {
		final HashSet<VarDecl<?>> result = new HashSet<>();
		result.addAll(extractVarsFromExprs(edge.guards));
		if (edge.sync.isPresent()) {
			final SyncLabel sync = edge.getSync().get();
			final Collection<VarDecl<?>> varDecls = extractVarsFromExpr(sync.getExpr());
			for (final VarDecl<?> varDecl : varDecls) {
				if (!isArrayOfChans(varDecl.getType())) {
					result.add(varDecl);
				}
			}
		}
		result.addAll(extractVarsFromStmts(edge.updates));
		return result;
	}

	private static boolean isArrayOfChans(final Type type) {
		if (type instanceof ChanType) {
			return true;
		} else if (type instanceof ArrayType) {
			final ArrayType<?, ?> arrayType = (ArrayType<?, ?>) type;
			return isArrayOfChans(arrayType.getElemType());
		} else {
			return false;
		}
	}

	////

	public static final class Loc {

		public static enum Kind {
			NORMAL, URGENT, COMMITED;
		}

		private final Collection<Edge> inEdges;
		private final Collection<Edge> outEdges;
		private final String name;
		private final Kind kind;
		private final Collection<Expr<BoolType>> invars;

		private final Collection<Edge> unmodInEdges;
		private final Collection<Edge> unmodOutEdges;

		private Loc(final String name, final Kind kind, final Collection<Expr<BoolType>> invars) {
			inEdges = new ArrayList<>();
			outEdges = new ArrayList<>();
			this.name = checkNotNull(name);
			this.kind = checkNotNull(kind);
			this.invars = ImmutableList.copyOf(checkNotNull(invars));

			unmodInEdges = Collections.unmodifiableCollection(inEdges);
			unmodOutEdges = Collections.unmodifiableCollection(outEdges);
		}

		public Collection<Edge> getInEdges() {
			return unmodInEdges;
		}

		public Collection<Edge> getOutEdges() {
			return unmodOutEdges;
		}

		public String getName() {
			return name;
		}

		public Kind getKind() {
			return kind;
		}

		public Collection<Expr<BoolType>> getInvars() {
			return invars;
		}
	}

	////

	public static final class Edge {
		private final Loc source;
		private final Loc target;
		private final Collection<Expr<BoolType>> guards;
		private final Optional<SyncLabel> sync;
		private final List<AssignStmt<?, ?>> updates;

		public Edge(final Loc source, final Loc target, final Collection<Expr<BoolType>> guards,
				final Optional<SyncLabel> sync, final List<AssignStmt<?, ?>> updates) {
			this.source = checkNotNull(source);
			this.target = checkNotNull(target);
			this.guards = ImmutableList.copyOf(checkNotNull(guards));
			this.sync = checkNotNull(sync);
			this.updates = ImmutableList.copyOf(updates);
		}

		public Loc getSource() {
			return source;
		}

		public Loc getTarget() {
			return target;
		}

		public Collection<Expr<BoolType>> getGuards() {
			return guards;
		}

		public Optional<SyncLabel> getSync() {
			return sync;
		}

		public List<AssignStmt<?, ?>> getUpdates() {
			return updates;
		}
	}

}