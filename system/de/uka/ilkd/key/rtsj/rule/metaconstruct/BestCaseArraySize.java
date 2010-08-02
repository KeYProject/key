package de.uka.ilkd.key.rtsj.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class BestCaseArraySize extends AbstractMetaOperator {
    
    public BestCaseArraySize() {
        super(new Name("#bcArraySize"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        final TermFactory tf = TermFactory.DEFAULT;

        final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
                
        Term sixteen = services.getTypeConverter().convertToLogicElement(new IntLiteral("16"));
        Term twelve  = services.getTypeConverter().convertToLogicElement(new IntLiteral("12"));
        
        if(convertToDecimalString(term.sub(0), services).equals("8")){
            return tf.createFunctionTerm(intLDT.getAdd(), sixteen, tf.createFunctionTerm(
                    intLDT.getMul(), term.sub(0), term.sub(1)));
        }else{
            return tf.createFunctionTerm(intLDT.getAdd(), twelve, tf.createFunctionTerm(
                    intLDT.getMul(), term.sub(0), term.sub(1)));            
        }
    }
}