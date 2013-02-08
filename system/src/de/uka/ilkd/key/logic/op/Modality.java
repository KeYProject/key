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

import java.util.HashMap;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * This class is used to represent a dynamic logic modality like
 * diamond and box (but also extensions of DL like
 * preserves and throughout are possible in the future).
 */
public final class Modality extends AbstractSortedOperator {

    private static final HashMap<String, Modality> nameMap 
    	= new HashMap<String, Modality>(10);
    
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


    /** 
     * A Java Card transaction version of the diamond modality. Means that a transaction is
     * currently underway.
     */    
    public static final Modality DIA_TRANSACTION = new Modality(new Name("diamond_transaction"));

    /** 
     * A Java Card transaction version of the box modality. Means that a transaction is
     * currently underway.
     */    
    public static final Modality BOX_TRANSACTION = new Modality(new Name("box_transaction"));

    /** 
     * The throughout operator of dynamic logic. A formula
     * [[alpha;]]Phi can be read as during processing the program alpha
     * Phi should hold at every step of execution. 
     */    
    public static final Modality TOUT = new Modality(new Name("throughout"));

    /** 
     * A Java Card transaction version of the throughout modality. Means that a transaction is
     * currently underway.
     */    
    public static final Modality TOUT_TRANSACTION = new Modality(new Name("throughout_transaction"));

    
    /** creates a modal operator with the given name
     * @param name the Name of the modality 
     */
    private Modality(Name name) {
	super(name, new Sort[]{Sort.FORMULA}, Sort.FORMULA, false);
	nameMap.put(name.toString(), this);
    }


    /**
     * Returns a modality corresponding to a string
     * @param str name of the modality to return
     */
    public static Modality getModality(String str) {
        return nameMap.get(str);
    }
    
    /** Whether this modality is termination sensitive,
     * i.e., it is a "diamond-kind" modality.
     * @return
     */
    public boolean terminationSensitive(){
        return (this == DIA || this == DIA_TRANSACTION);
    }
    
    /** Whether this is a transaction modality 
     */
    public boolean transaction(){
        return (this == BOX_TRANSACTION || this == DIA_TRANSACTION);
    }
}
