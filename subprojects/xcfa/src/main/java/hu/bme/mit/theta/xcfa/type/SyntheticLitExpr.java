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
package hu.bme.mit.theta.xcfa.type;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;

import java.util.Objects;

/**
 * Uses a recursive mutex
 * TODO implement wait/notify
 */
public final class SyntheticLitExpr extends NullaryExpr<SyntheticType> implements LitExpr<SyntheticType> {

	private final XCFA.Process lockedOn;
	/**
	 * num == -1 -> invalid state, error reached
	 * num == 0 -> valid state, unlocked
	 * num > 0 -> how many times has it been locked in this process (reentrant/recursive mutex)
	 */
	private final int num;

	private void checkState() {
		Preconditions.checkState(num != -1 || lockedOn == null);
		Preconditions.checkState(num != 0 || lockedOn == null);
		Preconditions.checkState(num <= 0 || lockedOn != null);
	}
	private SyntheticLitExpr(XCFA.Process lockedOn, int num) {
		if (num > 0)
			this.lockedOn = lockedOn;
		else
			this.lockedOn = null;
		this.num = num;
		checkState();
	}

	/** Lock is in invalid state, indicates error reached */
	public boolean isInvalid() {
		return num < 0;
	}

	public boolean isLocked() {
		return lockedOn != null;
	}

	public XCFA.Process getProcess() {
		return lockedOn;
	}

	public boolean isValid() {
		return !isInvalid();
	}

	private static class LazyHolder {
		private static final SyntheticLitExpr BOTTOM = new SyntheticLitExpr(null, -1);
		private static final SyntheticLitExpr INSTANCE = new SyntheticLitExpr(null, 0);
	}

	/** Means an invalid usage of locks */
	private static SyntheticLitExpr bottom() {
		return LazyHolder.BOTTOM;
	}

	public static SyntheticLitExpr unlocked() {
		return LazyHolder.INSTANCE;
	}

	public SyntheticLitExpr lock(XCFA.Process lockOn) {
		if (lockedOn == null) {
			return new SyntheticLitExpr(lockOn, 1);
		} else if (lockOn == lockedOn) {
			return new SyntheticLitExpr(lockedOn, num+1);
		}
		return bottom();
	}

	public SyntheticLitExpr unlock(XCFA.Process unlockOn) {
		if (lockedOn == null) {
			return bottom();
		} else if (unlockOn == lockedOn) {
			return new SyntheticLitExpr(lockedOn, num-1);
		}
		return bottom();
	}

	@Override
	public SyntheticType getType() {
		return SyntheticType.getInstance();
	}

	@Override
	public SyntheticLitExpr eval(Valuation val) {
		return this;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		SyntheticLitExpr that = (SyntheticLitExpr) o;
		return num == that.num &&
				Objects.equals(lockedOn, that.lockedOn);
	}

	@Override
	public int hashCode() {
		return Objects.hash(lockedOn, num);
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("SyntheticLitExpr").add(
				Utils.lispStringBuilder("LockedOn").add(lockedOn!=null ? lockedOn : "None")
		).add(
				Utils.lispStringBuilder("Times").add(num)
		).toString();
	}
}
