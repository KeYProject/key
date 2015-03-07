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

import java.io.Serializable;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.op.SchemaVariable;
/** this class encapsulates a SchemaVariable and its corresponding
 * instantiation if it is a JavaProgramElement. The class MapFrom...cannot
 * be used because of the different packages of the SchemaVariable and
 * the JavaProgramElement.
 */
public class ProgramSVEntry implements Serializable {
    
    /**
     * 
     */
    private static final long serialVersionUID = -5837249343101979072L;
    /** the SchemaVariable */
    private SchemaVariable key;
    /** the JavaProgramElement */
    private JavaProgramElement value;

    /** creates a new entry encapsulating the SchemaVariable key and its
     * JavaProgramElement instantiation value
     * @param key the SchemaVariable that is instantiated
     * @param value the JavaProgramElement 
     */ 
    public ProgramSVEntry(SchemaVariable key,
			  JavaProgramElement value) {
	this.key = key;
	this.value = value;
    }

    /** returns the SchemaVariable to be instantiated
     * @return the SchemaVariable to be instantiated
     */
    public SchemaVariable key() {
	return key;
    }
    
    /** returns true iff the keys and the mapped values are equal 
     * @return true iff the keys and the mapped values are equal  
     */
    public boolean equals(Object o) {
	if (!(o instanceof ProgramSVEntry)) {
	    return false;
	} 
	final ProgramSVEntry cmp = (ProgramSVEntry) o;
        return key().equals(cmp.key()) &&
                value().equals(cmp.value());
	}
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + key().hashCode();
    	result = 37 * result + value().hashCode();
    	return result;
    }
    
    /** returns the instantiation of the SchemaVariable
     * @return the instantiation of the SchemaVariable
     */
    public JavaProgramElement value() {
	return value;
    }

    /** toString */
    public String toString() {
	return "{"+key+"<--"+value+"}";
    }

}