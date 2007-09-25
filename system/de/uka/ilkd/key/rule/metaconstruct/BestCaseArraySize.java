package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class BestCaseArraySize extends AbstractMetaOperator {
    
    public BestCaseArraySize() {
        super(new Name("#bcArraySize"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        TermFactory tf = TermFactory.DEFAULT;
        Namespace funcs = services.getNamespaces().functions();
        Function add = (Function) funcs.lookup(new Name("add"));
        Function mul = (Function) funcs.lookup(new Name("mul"));
        
        IntLiteral lit = new IntLiteral("16");
        Term sixteen =  services.getTypeConverter().convertToLogicElement(lit);
        lit = new IntLiteral("12");
        Term twelve =  services.getTypeConverter().convertToLogicElement(lit);
        
        if(convertToDecimalString(term.sub(0), services).equals("8")){
            return tf.createFunctionTerm(add, sixteen, tf.createFunctionTerm(
                    mul, term.sub(0), term.sub(1)));
        }else{
            return tf.createFunctionTerm(add, twelve, tf.createFunctionTerm(
                    mul, term.sub(0), term.sub(1)));            
        }
    }
}