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

/** represents a name that is part of a program
 */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.ReferenceSuffix;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

public class ProgramElementName extends Name 
    implements TerminalProgramElement, Label, ReferenceSuffix, MethodName {

    private final String qualifierString;
    private final String shortName;
    private final NameCreationInfo creationInfo;
    private final Comment[] comments;

    /** create a new name
     * @param name the String with the name of the program element
     */
    public ProgramElementName(String name) {
	super(name);
	this.qualifierString = "".intern();
	this.shortName = name.intern();
        this.creationInfo = null;
	comments = new Comment[0];
    }

    /** create a new name
     * @param name the String with the name of the program element
     */
    public ProgramElementName(String name, Comment[] c) {
	super(name);
	this.qualifierString = "".intern();
	this.shortName = name.intern();
        this.creationInfo = null;
	comments = c;
    }

    public ProgramElementName(String name, NameCreationInfo creationInfo) {
	super(name);
	this.qualifierString = "".intern();
	this.shortName = name.intern();
        this.creationInfo = creationInfo;
	comments = new Comment[0];
    }

    public ProgramElementName(String name, NameCreationInfo creationInfo, Comment[] c) {
	super(name);
	this.qualifierString = "".intern();
	this.shortName = name.intern();
        this.creationInfo = creationInfo;
	comments = c;
    }

    public ProgramElementName(String n, String q) {
	super(q + "::" + n);
	assert q.length() > 0 : "Tried to create qualified name with missing qualifier";

	this.qualifierString = q.intern();
	this.shortName = n.intern();
        this.creationInfo = null;
	comments = new Comment[0];
    }

    public Comment[] getComments() {
	return comments;
    }
	
    /**
     * to be compatible to a ProgramElement
     */
    public SourceElement getFirstElement() {
	return this;
    }
	
	
    /**
     * to be compatible to a ProgramElement
     */
    public SourceElement getLastElement() {
	return this;
    }
	
    public void prettyPrint(PrettyPrinter w) throws java.io.IOException {
	w.printProgramElementName(this);
    }
	
    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnProgramElementName(this);
    }
	
	
    /**
       Returns the start position of the primary token of this element.
       To get the start position of the syntactical first token,
       call the corresponding method of <CODE>getFirstElement()</CODE>.
       @return the start position of the primary token.
    */
    public Position getStartPosition(){
	return Position.UNDEFINED;
    }
	
    /**
       Returns the end position of the primary token of this element.
       To get the end position of the syntactical first token,
       call the corresponding method of <CODE>getLastElement()</CODE>.
       @return the end position of the primary token.
    */
    public Position getEndPosition(){
	return Position.UNDEFINED;
    }
	
    /**
       Returns the relative position (number of blank heading lines and 
       columns) of the primary token of this element.
       To get the relative position of the syntactical first token,
       call the corresponding method of <CODE>getFirstElement()</CODE>.
       @return the relative position of the primary token.
    */
    public Position getRelativePosition(){
	return  Position.UNDEFINED;
    }
	
	
    public PositionInfo getPositionInfo(){
	return  PositionInfo.UNDEFINED;
    }
	
	
    /** equals modulo renaming is described in the corresponding
     * comment in class SourceElement. The ProgramElementName has to
     * check if an abstract name has been assigned and if, if both
     * elements are assigned to the same name, otherwise the names
     * have to be equal
     */
    public boolean equalsModRenaming(SourceElement se, 
				     NameAbstractionTable nat) {
	if (!(se instanceof ProgramElementName)) {
	    return false;
	}
	return nat.sameAbstractName(this, se);
    }
	
   	    
    public String getQualifier() {
	return qualifierString;
    }

    public String getProgramName() {
	return shortName;
    }

    public NameCreationInfo getCreationInfo() {
    	return creationInfo;
    }

    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (this.equals(src)) {
            source.next();
            return matchCond;
        } else {
            Debug.out("Program match failed (pattern, source)", this, src);
            return null;
        }        
    }
    
    @Override
    public boolean equals(Object o) {
	return super.equals(o);
    }
    
    @Override
    public int hashCode() {
	return super.hashCode();
    }
}