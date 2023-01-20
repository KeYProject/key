package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;


public final class MetaBinaryXOr extends MetaArithBitMaskOp {

    public MetaBinaryXOr() {
        super(new Name("#BinaryXOr"));
    }


    @Override
    protected BigInteger bitmaskOp(BigInteger left, BigInteger right) {
        return left.xor(right);
    }
}
