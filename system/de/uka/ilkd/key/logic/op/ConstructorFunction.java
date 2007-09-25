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


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.ArrayOfGenSort;
import de.uka.ilkd.key.logic.sort.GenSort;

/**
 * A <code>Constructor</code> is a <code>Function</code> which belongs to a generated sort.
 * A constructor's sort must be GenSort as well as the parameters.
 *
 * @author Sonja Pieper
 * @version 0.1, 07/08/01
 */

public class ConstructorFunction extends NonRigidFunction {
    
    /**
     * creates a new constructor with name, sort and param sorts.
     * @param name The name of the constructor
     * @param sort The sort of the constructor, this is the generated sort
     *        the constructor belongs to and which it 'generates'
     * @param aos The sorts of the parameters of the constructor, must also
     *        be generated sorts.
     */

    public ConstructorFunction(Name name, GenSort sort, ArrayOfGenSort aos){
	super(name,sort,aos);
    }

}
