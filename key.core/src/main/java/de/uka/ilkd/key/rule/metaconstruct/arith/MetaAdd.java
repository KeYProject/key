package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public final class MetaAdd extends AbstractTermTransformer {

    public MetaAdd() {
        super(new Name("#add"), 2);
    }

    public Term transform(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger bigIntArg1;
        BigInteger bigIntArg2;

        bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));

        BigInteger bigIntResult = bigIntArg1.add(bigIntArg2);

        return services.getTermBuilder().zTerm(bigIntResult.toString());
    }
}
