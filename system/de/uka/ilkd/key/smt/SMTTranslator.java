//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.smt.taclettranslation.TacletFormula;


public interface SMTTranslator {

    public static enum TERMPOSITION {ANTECEDENT, SUCCEDENT}
    
    /**
     * Translate a sequent.
     * @param sequent the sequent to translate.
     * @param services wrapper object for service attributes.
     * @return A StringBuffer representing the sequent in the given syntax.
     * @throws IllegalFormulaException if the sequent could not be translated.
     */
    public StringBuffer translate(Sequent sequent, Services services)
    		throws IllegalFormulaException;
    
    /**
     * Translate a term into the given syntax.
     * @param t The term to translate.
     * @param services a service wrapper object.
     * @return A StringBuffer, representing the term in the given syntax.
     * @throws IllegalArgumentException if the term is not of type FORMULA or could not be translated.
     */
    public StringBuffer translate(Term t, Services services) 
    		throws IllegalFormulaException;
    /**
     * Sets a assumption which has already the format of the used prover.  The assumptions is made of taclets.
     * Set the assumption before calling the general translate method. 
     * @param assumption
     */
    public void setTacletAssumptions(ImmutableList<TacletFormula> assumption);
    
    //TODO remove after testing!!
    /**
     * Caution! This Method is just for testing!! Do not use it, it might be removed very soon!!
     */
    public StringBuffer translateTerm (Term term, Vector<QuantifiableVariable> quantifiedVars,
	    Services services) throws IllegalFormulaException;
    
}
