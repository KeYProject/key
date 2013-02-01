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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SchemaVariable;


/** This class is used to store the instantiation of a schemavarible
 * if it is a name.
 */
public class NameInstantiationEntry extends InstantiationEntry {

    private final Name name;

   
    NameInstantiationEntry(SchemaVariable sv, Name name) {
	super(sv);
	this.name = name;
    }


    @Override
    public Object getInstantiation() {
	return name;
    }


    @Override
    public String toString() {
	return "[" + getSchemaVariable() + ", " + name + "]";
    }
}
