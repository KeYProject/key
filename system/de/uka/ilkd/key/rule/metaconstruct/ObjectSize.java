package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ObjectSize extends AbstractMetaOperator {

    public ObjectSize() {
        super(new Name("#objectSize"), 3);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        ProgramVariable consumed = services.getJavaInfo().getAttribute("consumed", 
                services.getJavaInfo().getKeYJavaTypeByClassName("javax.realtime.MemoryArea"));
        Namespace funcs = services.getNamespaces().functions();
        TermFactory tf = TermFactory.DEFAULT;
        Term heapSpaceTerm = tf.createAttributeTerm(consumed, term.sub(2));        
        IntLiteral objSizeLit = 
            new IntLiteral(services.getJavaInfo().getSizeInBytes(
        	    ((ProgramVariable) term.sub(0).op()).getKeYJavaType())+"");
        Term objSize = services.getTypeConverter().convertToLogicElement(objSizeLit);
        return tf.createUpdateTerm(heapSpaceTerm,
        	tf.createFunctionTerm((TermSymbol) funcs.lookup(new Name("add")),
        		heapSpaceTerm, objSize), term.sub(1));
    }

}
