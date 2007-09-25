// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;


/** Instances of this class represent named lemmata.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public class AsmLemma implements Named {

    /** The name (identifier) of the lemma */
    private final Name id;

    /** The formula of the lemma */
    private final Term phi;

    /** creates a new named lemma. */
    public AsmLemma(Name id, Term phi) {
	this.id = id;
	this.phi = phi;
    }

    /** returns the name of this named rule. This method is equal to
     * 'new Name(getId())'. */
    public Name name() {
	return id;
    }

    /** returns the name of this named rule. This method is equals to
     * 'name().toString()'. */
    public String getId() {
	return id.toString();
    }

    /** returns the formula of this lemma. The term is garantied
     * to be a formula */
    public Term getFormula() {
	return phi;
    }

    public String toString() {
	return "AsmLemma:name=" + id + ";formula=" + phi;
    }

}
