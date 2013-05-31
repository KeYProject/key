// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class ListInstantiation extends InstantiationEntry {

    /** the pe the schemavariable is instantiated with */
    private final ImmutableList<Object> list ;

   
    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param pes the List the 
     * SchemaVariable is instantiated with
     */
    ListInstantiation(SchemaVariable sv, ImmutableList<Object> pes) {
        super(sv);
        this.list = pes;
    }

 
    /** returns the intantiation of the SchemaVariable 
     * @return  the intantiation of the SchemaVariable 
     */
    public Object getInstantiation() {
        return list;
    }

    /** returns the intantiation of the SchemaVariable 
     * @return  the intantiation of the SchemaVariable 
     */
    public ImmutableList<Object> getList() {
        return list;
    }

    
    /** toString */
    public String toString() {
        return "["+getSchemaVariable()+", "+getInstantiation()+"]";
    }

}
