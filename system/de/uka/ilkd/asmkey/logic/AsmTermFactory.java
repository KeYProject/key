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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;

/** This class extends {@link de.uka.ilkd.key.logic.TermFactory}
 * by permitting the creation of AsmKey Specific Terms
 */
public class AsmTermFactory extends TermFactory {

    /** An instance of AsmTermFactory */
    public static final AsmTermFactory ASMDEFAULT = new AsmTermFactory();

    /** Creates an accT(s in t) term */
    public Term createAccTTerm(Term term1, Term term2) {
	return null;//AsmOperator.ACCT.createTerm(null, new Term[] {term1, term2});
    }

}
