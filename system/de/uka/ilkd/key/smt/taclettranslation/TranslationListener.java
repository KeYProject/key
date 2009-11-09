// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet.VariableSV;

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
    

}
