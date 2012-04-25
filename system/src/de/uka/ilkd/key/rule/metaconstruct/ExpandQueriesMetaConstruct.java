package de.uka.ilkd.key.rule.metaconstruct;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * Uses the class <code>QueryExpand</code> in order to insert query expansions in the term that the
 * meta construct is applied on. 
 * @author gladisch
 */
public class ExpandQueriesMetaConstruct extends AbstractTermTransformer {

	public static final String name= "#ExpandQueries";
	
    public ExpandQueriesMetaConstruct() {
    	super(new Name(name), 2);
    }

/** term.sub(0) is the term that possibly contains queries.
 *  term.sub(1) is expected to be true or false. True indicates that the 
 *  meta construct appears in a positive context wrt. to logical negation, (e.g. in the succedent or negated in the antecedent)
 *  False implies means that the meta construct appears in a negative context. (e.g. in the antecedent or negated in the succedent)
 */
   public Term transform(Term term, SVInstantiations svInst, Services services) {
    	Term arg1 = term.sub(0); 
    	Term arg2 = term.sub(1); //true or false. If true, than the application of the meta construct
    	boolean positiveContext;
    	if(arg2.op() == Junctor.TRUE){
    		positiveContext = true;
    	}else if (arg2.op() == Junctor.FALSE){
    		positiveContext = false;
    	}else {
    		throw new RuntimeException("Second argument of the meta construct "+name+ " must be true or false, but it is: "+arg2);
    	}
    	
    	return arg1;
    	
/*    	QueryExpand.INSTANCE.evaluateQueries(services, node, newGoal, term, positiveContext);
    	intArg1 = new
    	    BigInteger(convertToDecimalString(arg1, services));
    	intArg2 = new
    	    BigInteger(convertToDecimalString(arg2, services));
    	
    	Integer intResult = Integer.valueOf(intArg1.intValue() & intArg2.intValue());
    	
    	IntLiteral lit = new IntLiteral(intResult.toString());
    	return services.getTypeConverter().convertToLogicElement(lit);
*/
   }

}
