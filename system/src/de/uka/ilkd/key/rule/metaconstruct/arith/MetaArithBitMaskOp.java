package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public abstract class MetaArithBitMaskOp extends AbstractTermTransformer {

	public MetaArithBitMaskOp(Name name) {
		super(name, 2);
	}

	protected abstract BigInteger bitmaskOp(BigInteger left, BigInteger right);

	public Term transform(Term term, SVInstantiations svInst, Services services) {
		Term arg1 = term.sub(0);
		Term arg2 = term.sub(1);
		BigInteger left;
		BigInteger right;
	
		left = new
				BigInteger(convertToDecimalString(arg1, services));
		right = new
				BigInteger(convertToDecimalString(arg2, services));
	
		BigInteger result = bitmaskOp(left, right);
	
		IntLiteral lit = new IntLiteral(result.toString());
		return services.getTypeConverter().convertToLogicElement(lit);
	
	}

}