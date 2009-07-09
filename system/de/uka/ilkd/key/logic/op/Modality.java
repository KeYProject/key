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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * This class is used to represent a dynamic logic modality like
 * diamond and box (but also extensions of DL like
 * preserves and throughout are possible in the future).
 * For further information see @see PrpgramTerm.
 */

public final class Modality extends AbstractSortedOperator {

    private static final HashMap<String, Modality> nameMap = 
        new HashMap<String, Modality>(10);
    
    /** 
     * The diamond operator of dynamic logic. A formula
     * <alpha;>Phi can be read as after processing the program alpha
     * there exists a state such that Phi holds. 
     */    
    public static final Modality DIA = new Modality(new Name("diamond"));
    
    /** 
     * The box operator of dynamic logic. A formula
     * [alpha;]Phi can be read as 'In all states reachable
     * processing the program alpha the formula Phi holds'.
     */
    public static final Modality BOX = new Modality(new Name("box"));

    
    /** creates a modal operator with the given name
     * @param name the Name of the modality 
     */
    private Modality(Name name) {
	super(name, new Sort[]{Sort.FORMULA}, Sort.FORMULA);
	nameMap.put(name.toString(), this);
    }


    @Override
    public boolean isRigid () {
	return false;
    }


    /**
     * Returns a modality corresponding to a string
     * @param str name of the modality to return
     */
    public static Modality getModality(String str) {
        return (Modality)nameMap.get(str);
    }
}
