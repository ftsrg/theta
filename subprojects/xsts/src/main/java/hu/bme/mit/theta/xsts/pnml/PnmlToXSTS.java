package hu.bme.mit.theta.xsts.pnml;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.common.visualization.Node;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.TypeDecl;
import hu.bme.mit.theta.xsts.pnml.elements.*;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;

public class PnmlToXSTS {

	private  PnmlToXSTS(){
	}

	public static XSTS createXSTS(final PnmlNet net){

		final Map<String, VarDecl<IntType>> placeIdToVar = new HashMap<>();

		final List<Expr<BoolType>> initExprs = new ArrayList<>();
		// Create a variable for each place and initialize them
		for (PnmlPlace place: net.getPlaces()){
			final VarDecl<IntType> placeVar = Decls.Var(place.getName(),IntType.getInstance());
			placeIdToVar.put(place.getId(),placeVar);
			initExprs.add(Eq(placeVar.getRef(),Int(place.getInitialMarking())));
		}
		final Expr<BoolType> initExpr = And(initExprs);

		final List<Stmt> tranStmts = new ArrayList<>();
		// Create a transition for each variable
		for (PnmlTransition transition: net.getTransitions()){
			final List<Stmt> stmts = new ArrayList<>();

			// Check if enough tokens are present and remove input tokens
			for(PnmlArc inArc: transition.getInArcs()){
				final PnmlNode sourceNode = inArc.getSourceNode();
				checkArgument(sourceNode instanceof PnmlPlace,"Transition %s has an illegal source",transition.getId(),sourceNode.getId());
				final PnmlPlace sourcePlace = (PnmlPlace) sourceNode;

				final VarDecl<IntType> placeVar = placeIdToVar.get(sourcePlace.getId());
				final int weight = inArc.getWeight();

				final Stmt enoughTokens = AssumeStmt.of(GeqExpr.create2(placeVar.getRef(),Int(weight)));
				stmts.add(enoughTokens);

				final Stmt removeTokens = AssignStmt.of(placeVar,Sub(placeVar.getRef(),Int(weight)));
				stmts.add(removeTokens);
			}

			// Place output tokens
			for (PnmlArc outArc: transition.getOutArcs()){
				final PnmlNode targetNode = outArc.getTargetNode();
				checkArgument(targetNode instanceof PnmlPlace,"Transition %s has an illegal target %s",transition.getId(),targetNode.getId());
				final PnmlPlace targetPlace = (PnmlPlace) targetNode;

				final VarDecl<IntType> placeVar = placeIdToVar.get(targetPlace.getId());
				final int weight = outArc.getWeight();

				final Stmt placeTokens = AssignStmt.of(placeVar,Add(placeVar.getRef(),Int(weight)));
				stmts.add(placeTokens);
			}

			tranStmts.add(SequenceStmt.of(stmts));
		}

		final NonDetStmt tran = NonDetStmt.of(tranStmts);
		final NonDetStmt init = NonDetStmt.of(ImmutableList.of());
		final NonDetStmt env = NonDetStmt.of(ImmutableList.of());

		final Collection<TypeDecl> types = ImmutableList.of();
		final Map<VarDecl<?>, TypeDecl> varToType = ImmutableMap.of();
		final Set<VarDecl<?>> ctrlVars = ImmutableSet.of();

		return new XSTS(types,varToType,ctrlVars,init,tran,env,initExpr,True());
	}

}
