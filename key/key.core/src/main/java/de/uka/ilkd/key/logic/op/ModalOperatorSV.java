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

package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Schema variable matching modal operators.
 */
public final class ModalOperatorSV extends AbstractSV  {
    
    /** 
     * the set of modalities this sv can match 
     */
    private final ImmutableSet<Modality> modalities;    
    
    
    /** creates a new SchemaVariable that is used as placeholder for
     * modal operators.
     * @param name the Name of the SchemaVariable
     * @param modalities modal operators matched by this SV
     */    
    ModalOperatorSV(Name name, ImmutableSet<Modality> modalities) {
        super(name, new Sort[]{Sort.FORMULA}, Sort.FORMULA, false, false);
        this.modalities = modalities;
    }

    /**
     * returns an unmodifiable set of operators this schemavariable can match
     */
    public ImmutableSet<Modality> getModalities() {
        return modalities;
    }
    
    
    @Override
    public String toString() {
	return toString(" (modal operator)");
    }
    
    
    @Override 
    public String proofToString() {
	StringBuffer result = new StringBuffer();
	result.append("\\schemaVar \\modalOperator {");
        boolean first = true;
	for(Modality modality : modalities) {
            if(!first) {
              result.append(", ");
            }else{
              first = false;
            }
	    result.append(modality);
	}
	result.append("} ").append(name()).append(";\n");
	return result.toString();
    }
}