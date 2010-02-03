// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.SchemaVariable;



public class SVTypeInfo {

    private final SchemaVariable sv;
    private final KeYJavaType    type;

    public SVTypeInfo ( SchemaVariable p_sv,
			KeYJavaType    p_type ) {
	sv   = p_sv;
	type = p_type;
    }

    public SchemaVariable getSV   () {
	return sv;
    }

    public KeYJavaType    getType () {
	return type;
    }

    public boolean        equals  ( Object p ) {
	return
	    p instanceof SVTypeInfo &&
	    ((SVTypeInfo)p).getSV ()   == getSV () &&
	    ((SVTypeInfo)p).getType () == getType ();
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + getSV().hashCode();
    	result = 37 * result + getType().hashCode();
    	return result;
    }

    public String toString () {
    	return "" + sv + " type: " + type;
    }
}
