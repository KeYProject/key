// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;


/** Expression
 * taken from COMPOST and changed to achieve an immutable structure
 */
public interface Expression extends ProgramElement {

    /** 
     * returns the {@link KeYJavaType} of an expression 
     */
    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
