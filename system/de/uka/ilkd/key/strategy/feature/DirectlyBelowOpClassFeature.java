package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.op.Operator;
/**
 * The feature behaves in overall as @link {@link DirectlyBelowSymbolFeature} but tests
 * if the operator directly above belongs to a certain class of operators
 * 
 * TODO: eliminate this class and use term features instead
 */
public class DirectlyBelowOpClassFeature extends DirectlyBelowFeature {

    private DirectlyBelowOpClassFeature(Class badSymbol, int index) {
        super(badSymbol, index);      
    }
    
    public static Feature create(Class badSymbol) {
        return new DirectlyBelowOpClassFeature ( badSymbol, -1 );
    }
    
    public static Feature create(Class badSymbol, int index) {
        return new DirectlyBelowOpClassFeature ( badSymbol, index );
    }

    protected boolean isBadSymbol(Operator op) {        
        return ((Class)badSymbol).isInstance(op);
    }

}
