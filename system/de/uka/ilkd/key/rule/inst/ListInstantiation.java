// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.ListOfObject;

public class ListInstantiation extends InstantiationEntry {

    /** the pe the schemavariable is instantiated with */
    private final ListOfObject list ;

   
    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param pes the List the 
     * SchemaVariable is instantiated with
     */
    ListInstantiation(SchemaVariable sv, ListOfObject pes) {
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
    public ListOfObject getList() {
        return list;
    }

    
    /** toString */
    public String toString() {
        return "["+getSchemaVariable()+", "+getInstantiation()+"]";
    }

}
