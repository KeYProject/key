/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.assumptions;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;

/**
 * Listener for the classes which implement <code>TacletTranslator</code>. Use this interface to get
 * information while translating a taclet.
 */
public interface TranslationListener {
    /**
     * Called when the translator finds a term that have a sort. You can use this event to collect
     * all sorts that are used.
     *
     * @param sort the sort that has been found.
     */
    void eventSort(Sort sort);

    /**
     * Called when the translator finds a term that has a quantified variable. You can use this
     * event to collect all quantified variables that are used.
     *
     * @param var the quantified variable that has been found.
     */
    void eventQuantifiedVariable(QuantifiableVariable var);

    /**
     * Called when the translator finds a schema variable of type formula. You can use this event to
     * collect all schema variables of type formula that are used.
     *
     * @param formula
     */
    void eventFormulaSV(SchemaVariable formula);

    /**
     * Called when the translator can not instantiate a generic sort with a particular sort in the
     * given term. The result type determines whether the translation is aborted: The idea is, to
     * make the translation robust against invalid instantiation.
     *
     * @param dest the generic sort to instantiate
     * @param sort the instantiation sort.
     * @param t the taclet thats belongs to the term
     * @param term the term to be instantiated
     * @return return <code>true</code> if you want to terminate the translation of the taclet,
     *         otherwise <code>false<code>.
     */
    boolean eventInstantiationFailure(GenericSort dest, Sort sort, Taclet t, JTerm term);

}
