package hu.bme.mit.theta.xcfa.model.utils;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.PopStmt;
import hu.bme.mit.theta.core.stmt.PushStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class LabelUtils {

	public static boolean isGlobal(XcfaLabel label, XCFA xcfa) {
		return label instanceof XcfaLabel.FenceXcfaLabel || getVars(label).stream().anyMatch(varDecl -> xcfa.getGlobalVars().contains(varDecl));
	}

	public static Collection<VarDecl<?>> getVars(XcfaLabel xcfaLabel) {
		return xcfaLabel.accept(new XcfaLabelVisitor<Void, Collection<VarDecl<?>>>() {
			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.AtomicBeginXcfaLabel label, Void param) {
				return Set.of();
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.AtomicEndXcfaLabel label, Void param) {
				return Set.of();
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.ProcedureCallXcfaLabel label, Void param) {
				return label.getParams().stream().map(expr -> ExprUtils.getVars(expr).stream()).reduce(Streams::concat).map(varDeclStream -> varDeclStream.collect(Collectors.toSet())).orElse(Set.of());
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.StartThreadXcfaLabel label, Void param) {
				return Streams.concat(ExprUtils.getVars(label.getParam()).stream(), Stream.of(label.getKey())).collect(Collectors.toSet());
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.JoinThreadXcfaLabel label, Void param) {
				return Set.of(label.getKey());
			}

			@Override
			public <T extends Type> Collection<VarDecl<?>> visit(XcfaLabel.LoadXcfaLabel<T> label, Void param) {
				return Set.of(label.getGlobal(), label.getLocal());
			}

			@Override
			public <T extends Type> Collection<VarDecl<?>> visit(XcfaLabel.StoreXcfaLabel<T> label, Void param) {
				return Set.of(label.getGlobal(), label.getLocal());
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.FenceXcfaLabel label, Void param) {
				return Set.of();
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.StmtXcfaLabel label, Void param) {
				return StmtUtils.getVars(label.getStmt());
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.SequenceLabel sequenceLabel, Void param) {
				return sequenceLabel.getLabels().stream().map(LabelUtils::getVars).reduce((a, b) -> Streams.concat(a.stream(), b.stream()).collect(Collectors.toSet())).orElse(Set.of());
			}

			@Override
			public Collection<VarDecl<?>> visit(XcfaLabel.NondetLabel nondetLabel, Void param) {
				return nondetLabel.getLabels().stream().map(LabelUtils::getVars).reduce((a, b) -> Streams.concat(a.stream(), b.stream()).collect(Collectors.toSet())).orElse(Set.of());
			}

			@Override
			public Collection<VarDecl<?>> visit(SkipStmt stmt, Void param) {
				return Set.of();
			}

			@Override
			public Collection<VarDecl<?>> visit(AssumeStmt stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public <DeclType extends Type> Collection<VarDecl<?>> visit(AssignStmt<DeclType> stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public <DeclType extends Type> Collection<VarDecl<?>> visit(HavocStmt<DeclType> stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public Collection<VarDecl<?>> visit(SequenceStmt stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public Collection<VarDecl<?>> visit(NonDetStmt stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public Collection<VarDecl<?>> visit(OrtStmt stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public Collection<VarDecl<?>> visit(LoopStmt stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public <DeclType extends Type> Collection<VarDecl<?>> visit(PushStmt<DeclType> stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public <DeclType extends Type> Collection<VarDecl<?>> visit(PopStmt<DeclType> stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}

			@Override
			public Collection<VarDecl<?>> visit(IfStmt stmt, Void param) {
				return StmtUtils.getVars(stmt);
			}
		}, null);
	}

	public static void getAssortedVars(XcfaLabel label, Set<VarDecl<?>> assignedToVars, Set<VarDecl<?>> usedUpVars) {
		final Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> ret = Tuple2.of(assignedToVars, usedUpVars);
		label.accept(new XcfaLabelVarCollector(), Tuple2.of(assignedToVars, usedUpVars));
	}

	public static Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> getAssortedVars(XcfaLabel label) {
		Set<VarDecl<?>> assignedToVars = new LinkedHashSet<>();
		Set<VarDecl<?>> usedUpVars = new LinkedHashSet<>();
		getAssortedVars(label, assignedToVars, usedUpVars);
		return Tuple2.of(assignedToVars, usedUpVars);
	}

	public static boolean isNotLocal(XcfaLabel label, Map<VarDecl<?>, Optional<LitExpr<?>>> localVars) {
		return label instanceof XcfaLabel.FenceXcfaLabel || getVars(label).stream().anyMatch(varDecl -> !localVars.containsKey(varDecl));
	}
}
