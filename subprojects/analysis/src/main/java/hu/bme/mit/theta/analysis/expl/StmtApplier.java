/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.ArrayList;
import java.util.List;

final class StmtApplier {

	public static enum ApplyResult {
		FAILURE, SUCCESS, BOTTOM
	}

	private StmtApplier() {
	}

	public static ApplyResult apply(final Stmt stmt, final MutableValuation val, final boolean approximate) {
		if (stmt instanceof AssignStmt) {
			final AssignStmt<?> assignStmt = (AssignStmt<?>) stmt;
			return applyAssign(assignStmt, val, approximate);
		} else if (stmt instanceof AssumeStmt) {
			final AssumeStmt assumeStmt = (AssumeStmt) stmt;
			return applyAssume(assumeStmt, val, approximate);
		} else if (stmt instanceof HavocStmt) {
			final HavocStmt<?> havocStmt = (HavocStmt<?>) stmt;
			return applyHavoc(havocStmt, val, approximate);
		} else if (stmt instanceof SkipStmt) {
			final SkipStmt skipStmt = (SkipStmt) stmt;
			return applySkip(skipStmt);
		} else if (stmt instanceof SequenceStmt) {
			final SequenceStmt sequenceStmt = (SequenceStmt) stmt;
			return applySequence(sequenceStmt, val, approximate);
		} else if (stmt instanceof NonDetStmt) {
			final NonDetStmt nonDetStmt = (NonDetStmt) stmt;
			return applyNonDet(nonDetStmt, val, approximate);
		} else {
			throw new UnsupportedOperationException("Unhandled statement: " + stmt);
		}
	}

	private static ApplyResult applyAssign(final AssignStmt<?> stmt, final MutableValuation val,
										   final boolean approximate) {
		final VarDecl<?> varDecl = stmt.getVarDecl();
		final Expr<?> expr = ExprUtils.simplify(stmt.getExpr(), val);
		if (expr instanceof LitExpr<?>) {
			final LitExpr<?> lit = (LitExpr<?>) expr;
			val.put(varDecl, lit);
			return ApplyResult.SUCCESS;
		} else if (approximate) {
			val.remove(varDecl);
			return ApplyResult.SUCCESS;
		} else {
			return ApplyResult.FAILURE;
		}
	}

	private static ApplyResult applyAssume(final AssumeStmt stmt, final MutableValuation val,
										   final boolean approximate) {
		final Expr<BoolType> cond = ExprUtils.simplify(stmt.getCond(), val);
		if (cond instanceof BoolLitExpr) {
			final BoolLitExpr condLit = (BoolLitExpr) cond;
			if (condLit.getValue()) {
				return ApplyResult.SUCCESS;
			} else {
				return ApplyResult.BOTTOM;
			}
		} else {
			if (approximate) {
				return ApplyResult.SUCCESS;
			} else {
				return ApplyResult.FAILURE;
			}
		}
	}

	private static ApplyResult applyHavoc(final HavocStmt<?> stmt, final MutableValuation val,
										  final boolean approximate) {
		final VarDecl<?> varDecl = stmt.getVarDecl();
		val.remove(varDecl);
		return ApplyResult.SUCCESS;
	}

	private static ApplyResult applySkip(final SkipStmt skipStmt) {
		return ApplyResult.SUCCESS;
	}

	private static ApplyResult applySequence(final SequenceStmt stmt, final MutableValuation val,
											 final boolean approximate) {
		for(Stmt subStmt: stmt.getStmts()){
			ApplyResult res=apply(subStmt,val,approximate);
			if(res==ApplyResult.BOTTOM || res==ApplyResult.FAILURE) return res;
		}
		return ApplyResult.SUCCESS;
	}

	private static ApplyResult applyNonDet(final NonDetStmt stmt, final MutableValuation val,
											 final boolean approximate) {
		List<MutableValuation> valuations=new ArrayList<MutableValuation>();
		int successIndex=-1;
		for(int i=0; i<stmt.getStmts().size(); i++){
			MutableValuation subVal=MutableValuation.copyOf(val);
			ApplyResult res=apply(stmt.getStmts().get(i),subVal,approximate);
			if(res==ApplyResult.FAILURE) return ApplyResult.FAILURE;
			if(res==ApplyResult.SUCCESS){
				valuations.add(subVal);
				if(successIndex==-1)successIndex=i;
			}
		}
		if(valuations.size()==0){
			return ApplyResult.BOTTOM;
		} else  if(valuations.size()==1){
			return apply(stmt.getStmts().get(successIndex),val,approximate);
		} else if(approximate){
			apply(stmt.getStmts().get(successIndex),val,approximate);
			List<Decl> toRemove=new ArrayList<Decl>();
			for(Decl decl: val.getDecls()){
				for(MutableValuation subVal: valuations){
					if(!val.eval(decl).equals(subVal.eval(decl))){
						toRemove.add(decl);
						break;
					}
				}
			}
			for(Decl decl:toRemove) val.remove(decl);
			return ApplyResult.SUCCESS;
		} else{
			return ApplyResult.FAILURE;
		}
	}




}
