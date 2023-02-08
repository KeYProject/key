package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;


public final class MetaBinaryAnd extends MetaArithBitMaskOp {

    public MetaBinaryAnd() {
        super(new Name("#BinaryAnd"));
    }


    @Override
    protected BigInteger bitmaskOp(BigInteger left, BigInteger right) {
        return left.and(right);
    }
}
