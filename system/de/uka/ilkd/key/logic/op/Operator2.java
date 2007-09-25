// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Term;

/** The interface Operator2 enhances the Operator interface.
 *
 * @author Hubert Schmid
 */

public interface Operator2 extends Operator {

    /** This method creates a Term with this operator as top level
     * operator and the given subterms. This is also called "prototype
     * pattern".
     * @param vars all quantified variables. The operator should now
     * how to handle this. In most cases, the array will be empty.
     * @param terms the subterms
     * @return a term with this operator as top level operator and the
     * given subterms */
    Term createTerm(ArrayOfQuantifiableVariable vars, Term[] terms);

}
