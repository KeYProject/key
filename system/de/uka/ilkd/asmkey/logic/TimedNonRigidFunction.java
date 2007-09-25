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
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;


/** Dynamic (non-rigid) function with time argument for timed
 * logic.
 * 
 *
 * @author Stanislas Nanchen */

public final class TimedNonRigidFunction extends NonRigidFunction {


    /** creates a new instance with the given name, sort and sorts of
     * arguements. See {@link DynamicFunction#DynamicFunction(Name, Sort,
     * Sort[])}. */
    public TimedNonRigidFunction(Name name, Sort sort, Sort[] argSorts) {
        super(name, sort, argSorts);
    }

}
