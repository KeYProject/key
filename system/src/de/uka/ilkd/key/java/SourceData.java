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

package de.uka.ilkd.key.java;

/**
 * This class keeps track of the next element to match, which is provided by  
 * calling method {@link #getSource()}. The rough idea is to store the parent ast 
 * node and the index of the child which has to be matched (for convenience reasons 
 * <tt>-1</tt> encodes that the parent node itself has to be matched).
 * 
 * This kind of wrapping is useful when matching list schemavariables.
 */
public class SourceData {

    /**
     * the program element being either the parent of the program element to be matched or 
     * the element itself depending on the value of childPos
     */
    private ProgramElement element;
    
    /** the position of the children of element which has to be matched
     * against the pattern. If <tt>childPos</tt> is <tt>-1</tt> then <tt>element</tt> has to be matched.
     */
    private int childPos;

    /** the services */
    private final Services services;
    
    
    /**
     * creates a new source data object with parent node <tt>element</tt> whose 
     * <tt>childPos</tt>-th child has to be matched (-1 denotes <tt>element</tt> itself 
     * has to be matched 
     * @param element the ProgramElement 
     * @param childPos the int giving the index of the child of <tt>element</tt> to be matched
     * @param services the Services 
     */
    public SourceData(ProgramElement element, int childPos, Services services) {
	assert services != null;
	assert element != null;
        this.services = services;
        this.element  = element;
        this.childPos = childPos;
    }


    /**
     * returns index of the child to be matched
     * @return an int which is <tt>-1</tt> if @link #getElement() 
     * has to be matched itself otherwise it refers to the index of the child 
     * of <tt>element</tt> to be matched
     */
    public int getChildPos() {
        return childPos;
    }


    /**
     * sets the index of the child to be matched
     * @param childPos the int with the new index
     */
    public void setChildPos(int childPos) {
        this.childPos = childPos;
    }

    /**
     * returns always the parent node
     * @return the parent node
     */
    public ProgramElement getElement() {
        return element;
    }


    /**
     * sets the parent node
     * @param element the ProgramElement used as new parent node
     */
    public void setElement(ProgramElement element) {
        this.element = element;
    }
    
    /**
     * returns the element to be matched, i.e. if @link #getChildPos() is <tt>-1</tt> 
     * it returns @link #getElement()
     * otherwise it returns the getChildPos()-th child or <tt>null</tt> if the returned
     * child position is out of bound.  
     * @return the ProgramElement to be matched next or <tt>null</tt> if there is no such 
     * element
     */
    public ProgramElement getSource() {
        if (childPos == -1) return element;

        final NonTerminalProgramElement ntpe = 
            (NonTerminalProgramElement)element;
        
        if (childPos < ntpe.getChildCount()) {
            return ntpe.getChildAt(childPos);
        } else {
            return null;
        }    
    }
    
    /**
     * increments the child position by one, this means moving on to the next sibling 
     * (or the first child if childPos has been <tt>-1</tt> before     
     */
    public void next() {
        childPos++;        
    }

    /**
     * returns the services object 
     * @return the services object 
     */
    public Services getServices() {              
        return services;
    }

    /**
     * toString
     */
    public String toString() {
        return "Source:" + element + " child: " + childPos;
    }
    
}
