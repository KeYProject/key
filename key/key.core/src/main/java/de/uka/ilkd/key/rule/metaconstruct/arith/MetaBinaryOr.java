package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;


public final class MetaBinaryOr extends MetaArithBitMaskOp {

    public MetaBinaryOr() {
        super(new Name("#BinaryOr"));
    }


    @Override
    protected BigInteger bitmaskOp(BigInteger left, BigInteger right) {
        return left.or(right);
    }
}
