// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;


import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;

/**
 * A instance of <code>TacletTranslator</code> translates a single taclet to a
 * formula.
 */

public interface TacletTranslator {

    /**
     * Translates a taclet to a formula.
     * 
     * @param t
     *            taclet to be translated
     * @param sortsForGeneric this sorts are used for the instantiation of the generics sorts.
     * @return formula which expresses the meaning of the taclet.
     * @throw IllegalTacletException if the taclet is not translatable.
     */
    public TacletFormula translate(Taclet t, ImmutableSet<Sort> sortsForGeneric,
	    ImmutableSet<Term> attributeTerms, int maxGeneric) throws IllegalTacletException;
    
    /**
     * Adds a <code>TranslationListener</code> to the list of listener. For events that are called see <code>TranslationListener</code>.
     * @param listener listener to be added.
     */
    public void addListener(TranslationListener listener);
    
    /**
     * Removes the given listener from the list of listener.
     * @param listener
     */
    public void removeListener(TranslationListener listener);

}
