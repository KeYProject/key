// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ArrayOfIProgramVariable;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.ExtList;



/**
 * This class is used to represent atomic statements and expressions. Instances
 * of this class have no identity themselves, but they are instead provided an
 * instance of the class <code>ProgramSVSkolem</code> as operator symbol. The
 * relationship between <code>ProgramSVSkolem</code> and
 * <code>ProgramSVProxy</code> is similar to the relationship between
 * <code>Operator</code> and <code>Term</code>
 */
public class ProgramSVProxy
    implements NonTerminalProgramElement, Statement, Expression {
    

    private final ProgramSVSkolem         op;  

    private final ArrayOfIProgramVariable influencingPVs;
    private final ArrayOfStatement        jumpTable;


    public ProgramSVProxy ( ProgramSVSkolem         p_op,
			    ArrayOfIProgramVariable p_influencingPVs,
			    ArrayOfStatement        p_jumpTable ) {
	op             = p_op;
	influencingPVs = p_influencingPVs;
	jumpTable      = p_jumpTable;

	if ( !op.checkInfluencingPVs ( influencingPVs ) )
	    throw new IllegalArgumentException
		( "Illegal program variables given as children" );
	if ( !op.checkJumpTable      ( jumpTable ) )
	    throw new IllegalArgumentException ( "Illegal jump table given" );
    }


    public ProgramSVProxy ( ExtList p_children ) {
	this ( (ProgramSVSkolem)p_children.get ( ProgramSVSkolem.class ),
	       new ArrayOfIProgramVariable ( (IProgramVariable[])p_children.collect
					    ( IProgramVariable.class ) ),
	       new ArrayOfStatement        ( (Statement[])       p_children.collect
					    ( Statement.class ) ) );
    }
    
  
    public ProgramSVSkolem op () {
	return op;
    }

    public ArrayOfIProgramVariable getInfluencingPVs () {
	return influencingPVs;
    }

    public ArrayOfStatement getJumpTable () {
	return jumpTable;
    }


 /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
 */
    public int getChildCount() {
	return 1 + influencingPVs.size () + jumpTable.size ();
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
	if ( index == 0 )
	    return op;
	else if ( index <= influencingPVs.size () )
	    return influencingPVs.getIProgramVariable ( index - 1 );
	return jumpTable.getStatement ( index - 1 - influencingPVs.size () );
    }
    
    /**
     *Get comments.
     *@return the comments.
     */
    public Comment[] getComments() {
	return new Comment[0];
    }
   

    public KeYJavaType getKeYJavaType() {
	return op ().getKeYJavaType ();
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
	return getKeYJavaType ();
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	return getKeYJavaType ();
    }


    /**
     *        Finds the source element that occurs first in the source. 
     *        @return the first source element in the syntactical representation of
     *        this element, may be equals to this element.
     *        @see #getStartPosition()
    */
    public SourceElement getFirstElement() {
	return this;
    }


    /**
 *        Finds the source element that occurs last in the source. 
 *        @return the last source element in the syntactical representation of
 *        this element, may be equals to this element.
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
	v.performActionOnProgramSVProxy ( this );
    }

    /**
     * Pretty print.
     * @param w a pretty printer.
     * @exception IOException occasionally thrown.
     */
    public void prettyPrint(PrettyPrinter w) throws java.io.IOException {
	w.printProgramSVProxy ( this );
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
	if (this.getClass()!=se.getClass()) {
	    return false;
	}
	if (((NonTerminalProgramElement)se).
	    getChildCount()!=getChildCount()) {
	    return false;
	}	
	for (int i = 0; i<getChildCount(); i++) {
	    if (!(getChildAt(i)).equalsModRenaming
		(((NonTerminalProgramElement)se).getChildAt(i), nat)) {
		return false;
	    }
	}
	return true;
    }

    /** @return String representation of the constraint */
    public String toString () {
	String res = "" + op (). getProgramElementName () + "( ";
	int i;
	for ( i = 0; i != getChildCount (); ++i ) {
	    res += getChildAt ( i );
	    if ( i < getChildCount () - 1 )
		res += ", ";
	}
	return res + " )";
    }

    public PositionInfo getPositionInfo () {
        return PositionInfo.UNDEFINED;
    }

    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        // TODO Auto-generated method stub
        return null;
    }
}
