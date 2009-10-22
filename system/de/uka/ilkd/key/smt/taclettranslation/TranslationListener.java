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

import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * Listener for the classes which implement <code>TacletTranslator</code>. 
 * Use this interface to get information while translating a taclet.
 */
public interface TranslationListener {
    /**
     * Called when the translator finds a term that have a sort. 
     * You can use this event to collect all sorts that are used while translating. 
     * @param sort
     */
    public void eventSort(Sort sort);
    

}
