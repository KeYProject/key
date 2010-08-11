// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.util.HashSet;

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
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of quantified variables
     * @return the SchemaVariable
     */
    public static SchemaVariable createVariableSV(Name name,
						  Sort sort,
						  boolean listSV) {
	return new VariableSV(name, sort, listSV);
    }

    /** 
     * creates a SchemaVariable representing a term but not a formula
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the term the SchemaVariable will be
     * used to represent
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of terms
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas  
     * @param strictSV boolean indicating if the schemavariable is declared as strict
     * forcing exact type match
     * @return the SchemaVariable
     */
    public static SchemaVariable createTermSV(Name    name,
					      Sort    sort,
					      boolean listSV,
					      boolean rigidness, 
                                              boolean strictSV) {
	return new TermSV(name, sort, listSV, rigidness, strictSV);
    }

    /**
      * creates a SchemaVariable representing an operator 
      * @param name the Name of the SchemaVariable
      * @param arity the arity of the modal operators represented by this SV
      * param modalitylist the list of actual modalities to match this SV (right now box & diamond)
      * @return the SchemaVariable
      */
    public static SchemaVariable createOperatorSV(Name name,
            Class matchingType, Sort sort, int arity, HashSet operators) {
        if (matchingType == Modality.class) {
            return new ModalOperatorSV(name, arity, operators);
        } else {
            return new OperatorSV(name, sort, arity, operators);
        }
    }

    public static SchemaVariable createTermSV(Name    name,
					      Sort    sort,
					      boolean listSV) {
	return createTermSV(name, sort, listSV, false, false);
    }

    /** creates a SchemaVariable representing a formula 
     * @param name the Name of the SchemaVariable
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of formulas
     * @return the SchemaVariable
     */
    public static SchemaVariable createFormulaSV(Name    name,
						 boolean listSV,
						 boolean rigidness) {
	return new FormulaSV(name, listSV, rigidness);
    }

    public static SchemaVariable createFormulaSV(Name    name,
						 boolean listSV) {
	return createFormulaSV(name, listSV, false);
    }

    public static SchemaVariable createListSV(Name name, Class matchType){
	return new ListSV(name, matchType);
    }

    /** creates a SchemaVariable representing a program construct
     * @param name the ProgramElementName of the SchemaVariable
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of program constructs
     * @return the SchemaVariable
     */
    public static SchemaVariable createProgramSV(ProgramElementName name, 
						 ProgramSVSort s,
						 boolean listSV){
	return new ProgramSV(name, s, listSV);
    }


    /** 
     * creates a SchemaVariable representing a skolem term
     * @param name the Name of the SchemaVariable
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of skolem terms
     * @return the SchemaVariable
     */
    public static SchemaVariable createSkolemTermSV(Name name, 
						   Sort s,
						   boolean listSV){
	return new SkolemTermSV(name, s, listSV);
    }
}
