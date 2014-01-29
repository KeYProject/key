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


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;

/** A factory class for different Schema Variables 
 */
public class SchemaVariableFactory {

    private SchemaVariableFactory() {}
    
    /**
     * creates a SchemaVariable representing quantified variables 
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the variable the SchemaVariable will be
     * used to represent
     * @return the SchemaVariable
     */
    public static VariableSV createVariableSV(Name name,
				              Sort sort) {
	return new VariableSV(name, sort);
    }

    /** 
     * creates a SchemaVariable representing a term but not a formula
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the term the SchemaVariable will be
     * used to represent
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas  
     * @param strictSV boolean indicating if the schemavariable is declared as strict
     * forcing exact type match
     * @return the SchemaVariable
     */
    public static TermSV createTermSV(Name name,
			              Sort sort,
			              boolean rigidness, 
                                      boolean strictSV) {
	return new TermSV(name, sort, rigidness, strictSV);
    }
    

    /**
      * creates a SchemaVariable representing an operator 
      * @param name the Name of the SchemaVariable
      * @return the SchemaVariable
      */
    public static ModalOperatorSV createModalOperatorSV(Name name,
            						Sort sort, 
            						ImmutableSet<Modality> modalities) {
	return new ModalOperatorSV(name, modalities);
    }

    
    public static TermSV createTermSV(Name name, Sort sort) {
	return createTermSV(name, sort, false, false);
    }
    

    /** creates a SchemaVariable representing a formula 
     * @param name the Name of the SchemaVariable
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas
     * @return the SchemaVariable
     */
    public static FormulaSV createFormulaSV(Name name, boolean rigidness) {
	return new FormulaSV(name, rigidness);
    }

    
    public static FormulaSV createFormulaSV(Name name) {
	return createFormulaSV(name, false);
    }
    
    
    public static UpdateSV createUpdateSV(Name name) {
	return new UpdateSV(name);
    }
    

    /** creates a SchemaVariable representing a program construct
     */
    public static ProgramSV createProgramSV(ProgramElementName name, 
				            ProgramSVSort s,
				            boolean listSV) {
	return new ProgramSV(name, s, listSV);
    }


    /** 
     * creates a SchemaVariable representing a skolem term
     */
    public static SkolemTermSV createSkolemTermSV(Name name, Sort s) {
	return new SkolemTermSV(name, s);
    }
    
    /**
     * creates a LabelSchemaVariable
     */
    public static TermLabelSV createTermLabelSV(Name name) {
        return new TermLabelSV(name);
    }
}
