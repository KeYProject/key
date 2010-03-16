package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class MetaReentrantScope extends MetaField implements Location {

    public MetaReentrantScope() {
        super("#reentrantScope", false);
    }

    /** calculates the resulting term. 
     * @throws RuntimeException if <code>t.sub(0)</code> is no subtype of Object 
     */
    public Term calculate(Term term, SVInstantiations svInst, 
                          Services services) {  
  
        final Term t = term.sub(0);
      
        final KeYJavaType objectKJT = services.getJavaInfo().getJavaLangObject();
        if (!(t.sort().extendsTrans(objectKJT.getSort()))) {
           
            throw new RuntimeException("Error:" + this + ". Rules have to ensure that" +
                    "this meta operator is only applied on subtypes of java.lang.Object" +
                    ", but this is of type " + t.sort() );
        }
        
        return termFactory.createAttributeTerm(services.getJavaInfo().
                getAttribute(ImplicitFieldAdder.IMPLICIT_REENTRANT_SCOPE, objectKJT), t);
    }

 
    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

  
}
