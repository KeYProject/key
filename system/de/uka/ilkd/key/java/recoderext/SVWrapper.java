// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public interface SVWrapper {

    /**
     * sets the schema variable of sort statement
     * @param s the String
     */
    void setSV(SchemaVariable sv);

    /**
     * returns a String name of this meta construct.
     */
    SchemaVariable getSV();


}
