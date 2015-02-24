// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class ListInstantiation extends InstantiationEntry<ImmutableList<Object>> {

    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param pes the List the 
     * SchemaVariable is instantiated with
     */
    ListInstantiation(SchemaVariable sv, ImmutableList<Object> pes) {
        super(pes);
    }
}