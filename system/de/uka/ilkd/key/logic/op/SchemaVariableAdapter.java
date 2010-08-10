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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents the root of a schema variable hierarchy to be
 * express termstructures that match on logical terms. Schema variables
 * are used in Taclets where they act as placeholders for other
 * TermSymbols. The TermSymbols a SchemaVariable is allowed to match
 * is specified by their type and sort. If a match fits these
 * conditions can be checked using the method isCompatible(TermSymbol t)
 */
public abstract class SchemaVariableAdapter extends TermSymbol
    implements SchemaVariable {

    /** 
     * SchemaVariables are used as placeholder for other
     * TermSymbols. The allowed type of the symbols is stored here.
     */
    private final Class matchType;

    /**
     * this flag indicates if the schemavariable matches a list of syntactical
     * elements 
     */
    private final boolean listSV;


    /** 
     * creates a new SchemaVariable. That is used as placeholder for
     * TermSymbols of a certain type.
     * @param name the Name of the SchemaVariable
     * @param matchType Class representing the type of symbols that
     * can be matched
     * @param sort the Sort of the SchemaVariable and the matched type     
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of syntactical elements
     */    
    protected SchemaVariableAdapter(Name name,
				    Class matchType,
				    Sort sort,
				    boolean listSV) {
	super(name, sort);
	this.matchType = matchType;
	this.listSV    = listSV;
    }
    
    protected SchemaVariableAdapter(Name name,
				    Class matchType) {
        this(name, matchType, null, false);
    }
    

    /** 
     * this method tests on object identity
     */
    public boolean equalsModRenaming(SourceElement se, 
				     NameAbstractionTable nat) {
	return se == this;
    }
    
    public Class matchType() {
	return matchType;
    }

    /** returns true iff this SchemaVariable is used to match
     * bound (quantifiable) variables 
     * @return true iff this SchemaVariable is used to match
     * bound (quantifiable) variables 
     */
    public boolean isVariableSV() {
	return false;
    }

    /** returns true iff this SchemaVariable is used to match
     * a term but not a formula
     * @return true iff this SchemaVariable is used to match
     * a term but not a formula
     */
    public  boolean isTermSV() {
	return false;
    }


    /** returns true iff this SchemaVariable is used to match
     * a formula 
     * @return true iff this SchemaVariable is used to match
     * a formula
     */
    public boolean isFormulaSV() {
	return false;
    }

    /** returns true iff this SchemaVariable is used to match
     * a part of a program 
     * @return true iff this SchemaVariable is used to match
     * a part of a program
     */
    public boolean isProgramSV() {
	return false;
    }

    /**
     * returns true if the schemavariable can match a list of syntactical
     * elements 
     * @return true if the schemavariable can match a list of syntactical
     * elements 
     */
    public boolean isListSV() {
	return listSV;
    }


    /** 
     * @return true iff this SchemaVariable is used to match
     * modal operators
     */
    public boolean isOperatorSV() {
	return false;
    }
 
    /** returns true iff this SchemaVariable is used to match (create)
     * a skolem term
     * @return true iff this SchemaVariable is used to match (create)
     * a skolem term
     */
    public boolean isSkolemTermSV() {
	return false;
    }

    public boolean isNameSV() {
	return false;
    }

    /**
     * @return true if the schemavariable has the strict modifier 
     * which forces the instantiation to have exact the same sort
     * as the schemavariable (or if the sv is of generic sort - 
     * the instantiation of the generic sort)
     */
    public boolean isStrict () {
        return true; 
    }

    /** @return arity of the Variable as int */
    public int arity() {
	return 0;
    }
    
    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return isRigid ();
    }

    public boolean isRigid () {
	return false;
    } 

    /** toString */
    public String toString(String sortSpec) {
	return name()+" ("+sortSpec+")"; 
    }

    /* default toString for schema variables witho sortSpec, e.g. ModifiesSV */
    public String toString() {
	return name().toString(); 
    }
}
