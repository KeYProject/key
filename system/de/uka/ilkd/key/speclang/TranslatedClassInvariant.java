package de.uka.ilkd.key.speclang;

import java.io.IOException;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;

/**
 * @deprecated
 */
public class TranslatedClassInvariant  extends AbstractClassInvariant {

    private final Term translation;
    private final Services services;
    
    /**
     * Creates a class invariant.
     * @param modelClass the invariant's model class
     * @param inv the invariant in some specification language
     * @param translator a suitable translator for expressions of this 
     *                   specification language
     */
    public TranslatedClassInvariant(ModelClass modelClass,
                                    Term translation,
                                    Services services) {
	super(modelClass);
	this.translation = translation;
	this.services    = services;
    }
    

    public FormulaWithAxioms getInv(Services services) {
        return new FormulaWithAxioms(translation);
    }
    
    public FormulaWithAxioms getOpenInv(ParsableVariable selfVar, 
	      			      	Services services) {
	//not implemented
	assert false;
	return null;
    }

    
    public String toString() {
        LogicPrinter p = new LogicPrinter(new ProgramPrinter(), NotationInfo.createInstance(), services);
        try {
            p.printTerm(translation);
        } catch (IOException ioe) {
            return translation.toString();
        }
        return p.result().toString();
    }
}
