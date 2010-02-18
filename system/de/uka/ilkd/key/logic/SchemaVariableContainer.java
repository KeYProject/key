// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.op.SchemaVariable;


/**
 * Implement this interface for terms that contain 
 * SchemaVariables that would otherwise not be collected. 
 * 
 * @author mulbrich
 *
 */
public interface SchemaVariableContainer {

    ImmutableList<SchemaVariable> collectSV(ImmutableList<SchemaVariable> varList);

}
