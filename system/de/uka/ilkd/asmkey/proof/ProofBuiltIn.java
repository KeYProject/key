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


/** A ProofBuiltin represents an application of an built-in rule. The proof builtin
 * stores all required information, e.g. builtin name, selected formula/term, etc..
 *
 * @author Stanislas Nanchen */

public final class ProofBuiltIn extends ProofRule {

    ProofBuiltIn(String name, int formula, PosInTerm pos,
              boolean interactive) {
	super(name,formula,pos,interactive);
    }

}
