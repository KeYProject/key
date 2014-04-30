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

package de.uka.ilkd.key.java;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Top level implementation of a Java {@link NonTerminalProgramElement}.
 * taken from COMPOST and changed to achieve an immutable structure
 */
public abstract class JavaNonTerminalProgramElement 
			extends JavaProgramElement
 			implements NonTerminalProgramElement {

    
    private int hashCode;

    
    public JavaNonTerminalProgramElement() {
    }

    
    /**
     * Java program element.
     * @param list as ExtList with children of the node
     */
    public JavaNonTerminalProgramElement(ExtList list) {
        super(list);
    }

    
    public JavaNonTerminalProgramElement(PositionInfo pos) {
        super(pos);
    }

    
    public JavaNonTerminalProgramElement(ExtList children, PositionInfo pos) {
        super(children, pos);
    } 
    
    
    /**
     * returns the index of element el in array arr
     * @param arr the array where the element is looked for
     * @param el the element to look for 
     * @return the index of the element (-1 if not found)
     */
    protected int getArrayPos(ImmutableArray<ProgramElement> arr, ProgramElement el) {
	for (int i = 0, sz = arr.size() ;i<sz; i++) {
	    if (arr.get(i) == el) { 
		return i;
	    }
	} 
	return -1;
    } 

    
    /** commented in interface SourceElement. Overwrites the default
     * method implementation in ProgramElement by descending down to
     * the children.
     */
    public boolean equalsModRenaming(SourceElement se, 
				     NameAbstractionTable nat) {
	if (this.getClass() != se.getClass()) {
	    return false;
	}
	final JavaNonTerminalProgramElement jnte = (JavaNonTerminalProgramElement)se;
	
	if (jnte.getChildCount()!=getChildCount()) {
	    return false;
	}	
	
	for (int i = 0, cc = getChildCount(); i<cc; i++) {
	    if (!getChildAt(i).equalsModRenaming(jnte.getChildAt(i), nat)) {
		return false;
	    }
	}
	return true;
    }

    
    @Override    
    public boolean equals(Object o) {
        return super.equals(o);
    }
    
    
    @Override    
    public int hashCode(){
	if (hashCode == 0) {
	    int result = 17;
	    result = 37 * result + getChildCount();
	    for (int i = 0, cc = getChildCount(); i<cc; i++) {
	        result = 37 * result + getChildAt(i).hashCode();
	    }
	    if (result == 0) { 
		hashCode = 1;
	    } else {
		hashCode = result;
	    }
	}
    	return hashCode;
    }
    
  

    @Override    
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        
        Debug.out("Program match start (template, source)", this, src);
        
        if (src == null) {
            return null;
        }
        
        if (src.getClass() != this.getClass()) {
            Debug.out("Incompatible AST nodes (template, source)", 
                    this, src);
            Debug.out("Incompatible AST nodes (template, source)", 
                    this.getClass(), src.getClass());
            return null;
        }
        
        final NonTerminalProgramElement ntSrc = (NonTerminalProgramElement)src;        
        final SourceData newSource = new SourceData(ntSrc, 0, source.getServices());
                
        matchCond = matchChildren(newSource, matchCond, 0);

        if (matchCond == null) {
            return null;
        }
        
        source.next();        
        return matchCond;
    
    }
    
    
    /**
     * used by @link matchChildren to decide if a found match is valid or if there are remaining
     * source elements that have not been matched (in which case the match failed) 
     */
    protected boolean compatibleBlockSize(int pos, int max) {
        return pos >= max;
    }
    
    
    /**
     * matches successively all children of this current node. Thereby the
     * <tt>offset</tt>-th child is matched against <code>source.getSource()</code>. The call
     * <tt>source.next</tt> has to be done in the @link ProgramElement#match method
     * of the currently matched child in case of a successful match. This is 
     * <em>not</em> done here (rationale: schemavariables matching on lists can be 
     * implemented easy).
     * 
     *    
     * @param source the SourceData with the children to be matched
     * @param matchCond the MatchConditions found so far
     * @param offset the int denoting the index of the child to start with
     * @return the resulting match conditions or <tt>null</tt> if matching failed 
     */
    protected MatchConditions matchChildren(SourceData source,             
            MatchConditions matchCond, int offset) {             
                
        for (int i = offset, sz = getChildCount(); i<sz; i++) {             
            matchCond = getChildAt(i).match(source, matchCond);            
            if (matchCond == null) {
                return null;
            }
        }

        final NonTerminalProgramElement ntSrc = (NonTerminalProgramElement) source.getElement();

        if (!compatibleBlockSize(source.getChildPos(), ntSrc.getChildCount())) {
            Debug.out("Source has unmatched elements.");
            return null;
        }

        return matchCond;
    }        
}