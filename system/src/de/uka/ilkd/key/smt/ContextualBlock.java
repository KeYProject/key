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

package de.uka.ilkd.key.smt;



/**
 * The class <code>ContextualBlock</code> is used to integrate comments to translations of AbstractSMTtranslator. A concrete instance of <code>ContexualBlock</code>
 * describes either a block of semantical connected assumptions or a block of semantical connected predicates. 
 * How the assumptions or predicates are connected are described by the constants declared within this class. 
 * Concrete instances of AbstractSMTTranslator which implements the function    
 * <br><br>
 * <code>buildCompleteText(StringBuffer formula,
 *	    ArrayList<StringBuffer> assumptions,
 *	    ArrayList<ContextualBlock> assumptionBlocks,
 *	    ArrayList<ArrayList<StringBuffer>> functions,
 *	    ArrayList<ArrayList<StringBuffer>> predicates,
 *	    ArrayList<ContextualBlock> predicateBlocks,
 *	    ArrayList<StringBuffer> types, SortHierarchy sortHierarchy)</code><br><br> 
 * can use <code>assumptionBlocks</code> and <code>predicateBlocks</code> to find out, at which position in the containers <code>assumptions</code> 
 * and <code>predicates</code> blocks begin and end.  
 */
class ContextualBlock {
 
    /**
     * The block contains assumptions for function definitions. 
     */
    public static final int ASSUMPTION_FUNCTION_DEFINTION = 0;
    /**
     * The block contains assumptions for the type hierarchy. 
     */
    public static final int ASSUMPTION_TYPE_HIERARCHY = 1;
    /**
     *  The block contains assumptions for sorts which are expressed by predicates. 
     */
    public static final int ASSUMPTION_SORT_PREDICATES = 2;    
    /**
     *  The block contains assumptions for dummy variables. 
     */
    public static final int ASSUMPTION_DUMMY_IMPLEMENTATION = 3;
    
    public static final int ASSUMPTION_TACLET_TRANSLATION = 4;
    
    public static final int ASSUMPTION_DISTINCT = 5;
    
    public static final int ASSUMPTION_INTEGER = 6;
    
    
    public static final int ASSUMPTION_MULTIPLICATION = 7;
    
    public static final int ASSUMPTION_SORTS_NOT_EMPTY = 8;
    
    
    
    /**
     *  The block contains predicates which appear in the formula. 
     */
    public static final int PREDICATE_FORMULA = 0;
    /**
     *  The block contains predicates which describe types. 
     */
    public static final int PREDICATE_TYPE = 1;
    
    private int Start; 
    private int End; 
    private int Type;
    
    /**
     * 
     * @param start first index of the block
     * @param end last index of the block 
     * @param type type of the block
     */
    public ContextualBlock(int start, int end, int type) {
	super();
	Start = start;
	End = end;
	Type = type;
    }
    
    /** 
     * @return first index of the block 
     */
    public int getStart() {
        return Start;
    }
    /**
     * @return last index of the block
     */
    public int getEnd() {
        return End;
    }
    
    /**
     * Returns the type of the block, that can be
     * <br> 
     * - ASSUMPTION_FUNCTION_DEFINTION
     * <br> 
     * - ASSUMPTION_TYPE_HIERARCHY
     * <br>
     * - ASSUMPTION_SORT_PREDICATES
     * <br>
     * - ASSUMPTION_DUMMY_IMPLEMENTATION3
     * <br>
     * - PREDICATE_FORMULA
     * <br>
     * - PREDICATE_TYPE 
     * @return Type of the block
     */
    public int getType() {
        return Type;
    }
    

}