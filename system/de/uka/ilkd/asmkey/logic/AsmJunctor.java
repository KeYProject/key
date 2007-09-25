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
import de.uka.ilkd.key.logic.op.Junctor;


/** This class proproses 2 new Junctors (as static member)
 * the short circuit or and the short circuit and.
 *
 * @author Stanislas Nanchen
 */
public class AsmJunctor extends Junctor {

    /* new junctors */

    /** short circuit and */
    //public static final AsmJunctor ORELSE = new AsmJunctor(new Name("orelse"), 2);

    /** short circuit or */
    //public static final AsmJunctor ANDALSO = new AsmJunctor(new Name("andalso"), 2);

    /** modal operator for timed formulae #phi^t */
    //public static final Operator2 TIMED =
    //	new AsmOperator("timed", Sort.FORMULA, new Sort[] {Sort.FORMULA, null});
   
    public static final AsmJunctor TIMED = new AsmJunctor(new Name("timed"), 2);

    AsmJunctor(Name name, int arity) {
	super(name, arity);
    }

}
