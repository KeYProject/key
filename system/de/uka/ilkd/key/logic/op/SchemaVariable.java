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

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;

public interface SchemaVariable extends Operator {

    /** 
     * this method tests on object identity
     */
    boolean equalsModRenaming(SourceElement se, 
			      NameAbstractionTable nat);
    
    
    Class matchType();

    /** returns true iff this SchemaVariable is used to match
     * bound (quantifiable) variables 
     * @return true iff this SchemaVariable is used to match
     * bound (quantifiable) variables 
     */

    boolean isVariableSV();

    /** returns true iff this SchemaVariable is used to match
     * a term but not a formula
     * @return true iff this SchemaVariable is used to match
     * a term but not a formula
     */
    boolean isTermSV();

    /** returns true iff this SchemaVariable is used to match
     * a formula 
     * @return true iff this SchemaVariable is used to match
     * a formula
     */
    boolean isFormulaSV();

    /** returns true iff this SchemaVariable is used to match
     * a part of a program 
     * @return true iff this SchemaVariable is used to match
     * a part of a program
     */
    boolean isProgramSV();

    /**
     * returns true if the schemavariable can match a list of syntactical
     * elements 
     * @return true if the schemavariable can match a list of syntactical
     * elements 
     */
    boolean isListSV();

    /** 
     * @return true iff this SchemaVariable is used to match
     * modal operators
     */
    boolean isOperatorSV();
 
    /** returns true iff this SchemaVariable is used to match (create)
     * a skolem term
     * @return true iff this SchemaVariable is used to match (create)
     * a skolem term
     */
    boolean isSkolemTermSV(); 
    
    /** returns true iff this SchemaVariable is used to store a name
     * (e.g. of taclets or metavariables).
     * This SV is never matched against anything in the sequent.
     */
    boolean isNameSV();

    /** @return arity of the Variable as int */
    int arity(); 

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    boolean isRigid (Term term);

    /**     
     */
    boolean isRigid ();


}
