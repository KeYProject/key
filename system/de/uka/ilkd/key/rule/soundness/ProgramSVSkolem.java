// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import java.io.IOException;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.JumpStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ArrayOfIProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;



/**
 * This class represents statement and expression skolem symbols, which can be
 * used within programs. Instances of (the subclasses of) this class can be
 * used as operator together with the class <code>ProgramSVProxy</code>
 */
public abstract class ProgramSVSkolem
    implements StateDependingObject, NonTerminalProgramElement {

    private final ProgramElementName name;

    private final ArrayOfKeYJavaType influencingPVTypes;
    private final int                jumpCnt;


    /**
     * @param p_name The name of the symbol
     * @param p_influencingPVTypes An array of the types of the program variable
     * arguments
     * @param p_jumpCnt the size of the jump table
     */
    public ProgramSVSkolem ( ProgramElementName p_name,
			     ArrayOfKeYJavaType p_influencingPVTypes,
			     int                p_jumpCnt ) {
	name               = p_name;
	influencingPVTypes = p_influencingPVTypes;
	jumpCnt            = p_jumpCnt;
    }


    public ArrayOfKeYJavaType getInfluencingPVTypes () {
	return influencingPVTypes;
    }

    public int getJumpCount () {
	return jumpCnt;
    }

    public boolean checkJumpTable ( ArrayOfStatement p_jumpTable ) {
	if ( getJumpCount () != p_jumpTable.size () )
	    return false;

	int i = getJumpCount ();
	while ( i-- != 0 ) {
	    if ( !( p_jumpTable.getStatement ( i ) instanceof SchemaVariable ||
		    p_jumpTable.getStatement ( i ) instanceof JumpStatement ) )
		return false;
	}

	return true;
    }

    public boolean checkInfluencingPVs
        ( ArrayOfIProgramVariable p_influencingPVs ) {
	if ( getInfluencingPVTypes ().size () != p_influencingPVs.size () )
	    return false;

	int i;
	for ( i = 0; i != p_influencingPVs.size (); ++i ) {
	    if ( !( p_influencingPVs.getIProgramVariable ( i ) instanceof SchemaVariable ||
		    p_influencingPVs.getIProgramVariable ( i ).getKeYJavaType () ==
		    getInfluencingPVTypes ().getKeYJavaType ( i ) ) )
		return false;
	}
	
	return true;
    }

    public ProgramElementName getProgramElementName () {
	return name;
    }

 /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
 */
    public int getChildCount() {
	return 1;
    }

 /**
 *      Returns the child at the specified index in this node's "virtual"
 *      child array.
 *      @param index an index into this node's "virtual" child array
 *      @return the program element at the given position
 *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
 *                 of bounds
 */
    public ProgramElement getChildAt(int index) {
	return getProgramElementName ();
    }
    
    /**
     *Get comments.
     *@return the comments.
     */
    public Comment[] getComments() {
	return new Comment[0];
    }
   

    public KeYJavaType getKeYJavaType() {
	return null;
    }


    /**
     *        Finds the source element that occurs first in the source. 
     *        @return the first source element in the syntactical representation of
     *        this element, may be equals to this element.
     *        @see #toSource()
     *        @see #getStartPosition()
    */
    public SourceElement getFirstElement() {
	return this;
    }


    /**
 *        Finds the source element that occurs last in the source. 
 *        @return the last source element in the syntactical representation of
 *        this element, may be equals to this element.
 *        @see #toSource()
 *        @see #getEndPosition()
    */
    public SourceElement getLastElement() {
	return this;
    }

   /**
       Returns the start position of the primary token of this element.
       To get the start position of the syntactical first token,
       call the corresponding method of <CODE>getFirstElement()</CODE>.
       @return the start position of the primary token.
     */
    public Position getStartPosition() {
	return Position.UNDEFINED;
    }

    /**
       Returns the end position of the primary token of this element.
       To get the end position of the syntactical first token,
       call the corresponding method of <CODE>getLastElement()</CODE>.
       @return the end position of the primary token.
     */
    public Position getEndPosition() {
	return Position.UNDEFINED;
    }

    /**
       Returns the relative position (number of blank heading lines and 
       columns) of the primary token of this element.
       To get the relative position of the syntactical first token,
       call the corresponding method of <CODE>getFirstElement()</CODE>.
       @return the relative position of the primary token.
     */
    public Position getRelativePosition() {
	return Position.UNDEFINED;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnProgramSVSkolem ( this );
    }

    /**
     * Pretty print.
     * @param w a pretty printer.
     * @exception IOException occasionally thrown.
     */
    public void prettyPrint(PrettyPrinter w) throws java.io.IOException {
	w.printProgramElementName ( getProgramElementName () );
    }


    /**
     * This method returns true if two program parts are equal modulo
     * renaming. The equality is mainly a syntactical equality with
     * some exceptions: if a variable is declared we abstract from the
     * name of the variable, so the first declared variable gets
     * e.g. the name decl_1, the second declared decl_2 and so on.
     * Look at the following programs:
     * {int i; i=0;} and { int j; j=0;} these would be seen like
     * {int decl_1; decl_1=0;} and {int decl_1; decl_1=0;} which are
     * syntactical equal and therefore true is returned (same thing for
     * labels). But {int i; i=0;} and {int j; i=0;} (in the second
     * block the variable i is declared somewhere outside)
     * would be seen as {int decl_1; decl_1=0;} for the first one but 
     * {int decl_1; i=0;} for the second one. These are not
     * syntactical equal, therefore false is returned. 
     */
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
	return this == se;
    }
}
