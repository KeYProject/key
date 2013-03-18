// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.taclettranslation.assumptions;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;

/** 
 * Listener for the classes which implement <code>TacletTranslator</code>. 
 * Use this interface to get information while translating a taclet.
 */
public interface TranslationListener {
    /**
     * Called when the translator finds a term that have a sort. 
     * You can use this event to collect all sorts that are used. 
     * @param sort the sort that has been found.
     */
    public void eventSort(Sort sort);
    
    /**
     * Called when the translator finds a term that has a quantified variable.
     * You can use this event to collect all quantified variables that are used.
     * @param var the quantified variable that has been found.
     */
    public void eventQuantifiedVariable(QuantifiableVariable var);
    
    /**
     * Called when the translator finds a schema variable of type formula.
     * You can use this event to collect all schema variables of type formula that are used.
     * @param formula
     */
    public void eventFormulaSV(SchemaVariable formula);
    
    /**
     * Called when the translator can not instantiate a generic sort
     * with a particular sort in the given term.
     * The result type determines whether the
     * translation is aborted: The idea is, to make the translation 
     * robust against invalid instantiation. 
     * @param dest the generic sort to instantiate
     * @param sort the instantiation sort.
     * @param t the taclet thats belongs to the term
     * @param term the term to be instantiated
     * @return return <code>true</code> if you want to terminate the translation
     * of the taclet, otherwise <code>false<code>.
     */
    public boolean eventInstantiationFailure(GenericSort dest, Sort sort, Taclet t, Term term);

}
