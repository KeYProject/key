// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.Statement;

/**
 *  Constructor reference.
 *  @author <TT>AutoDoc</TT>
 */

public interface ConstructorReference extends MemberReference, Statement {

    /**
     *      Get arguments.
     *      @return the array wrapper of the argument expressions .
     */
    ArrayOfExpression getArguments();

}
