package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class MetaInstance extends AbstractMetaOperator {

    String type;
    
    public MetaInstance(){
        super(new Name("#instance"), 1);
    }
    
    public MetaInstance(String type) {
        super(new Name("#instance"+type), 1);
        this.type = type;
    }
    
    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Name name = new Name(type.replaceAll("_", ".") + "::instance");
        Function instanceFunc = (Function) services.getNamespaces().functions().lookup(name);
        Term instanceTerm = termFactory.createFunctionTerm(instanceFunc, term.sub(0));
        Term trueLitTerm = services.getTypeConverter().convertToLogicElement(BooleanLiteral.TRUE);
        return termFactory.createEqualityTerm(instanceTerm, trueLitTerm);
    }
    
    public MetaOperator getParamMetaOperator(String param) {
        MetaOperator mop = name2metaop("#instance_"+param);
        if(mop != null)
          return mop;
        return new MetaInstance(param);
     }
    
    public Sort sort() {
        return Sort.FORMULA;
    }
    
    public Sort sort(Term[] term) {
        return sort();
    }
    
}
