// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.util.HashMap;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/** this class is used to represent a dynamic logic modality like
 * diamond and box (but also extensions of DL like
 * preserves and throughout are possible in the future).
 * For further information see @see PrpgramTerm.
 */

public class Modality extends Op implements NonRigid {

    private static final HashMap<String, Modality> nameMap = 
        new HashMap<String, Modality>(10);
    
    private int arity=0;

    /** creates a modal operator with the given name and default arity
     * @param name the Name of the modality 
     */
    Modality(Name name) {
	super(name);
	this.arity = 1;
	nameMap.put(name.toString(), this);
    }

    /** creates a modal operator with the given name and arity
     * @param name the Name of the modality 
     * @param arity the arity of the modality 
     */
    Modality(Name name, int arity) {
	super(name);
	this.arity = arity;
	nameMap.put(name.toString(), this);
    }

    public static HashMap<String, Modality> getNameMap() {
	return nameMap;
    }

    /** @return Sort.FORMULA
     */
     public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }  

    /**
     * for convenience reasons 
     * @return Sort.FORMULA
     */
     public Sort sort(Term term) {
        return Sort.FORMULA;
    }  

    /** @return true if the subterm at postion 0 of the given term 
     * has Sort.FORMULA and the arity of the term is 1.
     */
    public boolean validTopLevel(Term term){
	if (term.arity()!=1) return false;
        return term.sub(0).sort().equals(Sort.FORMULA);
    }

    /** @return arity of the Diamond operator as int */
    public int arity() {
	return this.arity;
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return
	    super.isRigid ( term ) &&
	    term.javaBlock ().isEmpty();
    }

}
