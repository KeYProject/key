// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;


import de.uka.ilkd.key.logic.PosInTerm;


/** A ProofRule represents an application of an taclet. The proof rule
 * stores all required information, e.g. taclet name, selected term
 * and user instantiations.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public abstract class ProofRule {

    /** name of the taclet */
    private final String name;

    /** selected formula */
    private final int formula;

    /** selected subterm */
    private final PosInTerm pos;

    private final boolean interactive;


    ProofRule(String name, int formula, PosInTerm pos,
              boolean interactive) {
        this.name = name;
        this.formula = formula;
        this.pos = pos;
        this.interactive = interactive;
    }


    /** Name of used taclet. */
    public String getName() {
        return name;
    }

    /** Selected formula. */
    public int getFormula() {
        return formula;
    }

    /** Selected subterm. */
    public PosInTerm getPosition() {
        return pos;
    }

    public boolean isInteractive() {
        return interactive;
    }

}
