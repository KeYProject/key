package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;

/**
 * this termfeature returns <tt>ZERO</tt> costs if the given term 
 * is non-rigid 
 */
public class IsNonRigidTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new IsNonRigidTermFeature();    
    
    private IsNonRigidTermFeature () {}
    
    protected boolean filter(Term term) {        
        return !term.isRigid();
    }

}
