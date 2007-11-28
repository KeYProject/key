// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.Vector;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.jml.JMLSpec;

public interface JMLPOAndSpecProvider{

    Vector getMethodSpecs(String className, String methodName, 
			  ListOfString signature);

    /**
     * Creates a proof obligation for <code>spec</code>.
     * @param allInv true iff it should be assumed that every invariant of
     * every class holds for all existing object in the prestate of the method
     * that is specified by <code>spec</code>.
     * @param invPost if true, the applicable invariants are added to the 
     * postcondition.
     * @param assignable if true, a proof obligation for the assignable clause
     * of <code>spec</code> is created.
     */
    void createPOandStartProver(JMLSpec spec, boolean allInv, boolean invPost,
				boolean assignable);

}
