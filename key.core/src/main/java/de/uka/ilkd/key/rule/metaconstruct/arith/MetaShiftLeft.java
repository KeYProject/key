package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;

public class MetaShiftLeft extends MetaShift {

	public MetaShiftLeft() {
		super(new Name("#ShiftLeft"));
	}

	@Override
	protected BigInteger shiftOp(BigInteger left, BigInteger right) {
		return left.shiftLeft(right.intValue());
	}

}
