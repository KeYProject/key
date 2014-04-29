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

package de.uka.ilkd.key.java.statement;


import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.NameReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Label jump statement.
 * 
 */

public abstract class LabelJumpStatement extends JumpStatement implements NameReference {

    /**
     *      Name.
     */

    protected final Label name;

    /**
     *      Label jump statement.
     */

    public LabelJumpStatement() {
	name=null;
    }

    /**
     *      Label jump statement.    
     * @param label the Label of this jump statement
     */

    public LabelJumpStatement(Label label) {
	super();
	name=label;

    }
    
   /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     */
    public LabelJumpStatement(ExtList children) {
	super(children);
	name=children.get(Label.class);
    }



    /**
     *      Get name.
     *      @return the string.
     */
    public final String getName() {
        return (name == null) ? null : name.toString();
    }

    /**
     *      Get Label.
     *      @return the Label label
     */

    public Label getLabel() {
        return name;
    }


    /**
     *      Get identifier.
     *      @return the identifier.
     */
    public ProgramElementName getProgramElementName() {
	if ((name instanceof ProgramElementName) || (name==null)) {
	    return (ProgramElementName) name;
	}
	return null;
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return (name != null) ? 1 : 0;
    }

    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (name != null) {
            if (index == 0) return name;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


}