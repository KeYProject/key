// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Super constructor reference.
 *  
 */

public class SuperConstructorReference
    extends SpecialConstructorReference
    implements ReferenceSuffix {

   
    /**
     *  Access path to enclosing class. 
     *  As KeY normalises inner classes this should be always null and may be
     *  removed in future
     */
    protected final ReferencePrefix prefix;
   

    /**
     *      Super constructor reference.
     */
    public SuperConstructorReference() {
	prefix = null;
    }


    /**
     *      Super constructor reference.
     *      @param arguments an expression mutable list.
     */
    public SuperConstructorReference(Expression[] arguments) {
        super(arguments);
	this.prefix = null;
    }

    /**
     *      Super constructor reference.
     *      @param accessPath a reference prefix.
     *      @param arguments an expression mutable list.
     */

    public SuperConstructorReference(ReferencePrefix accessPath,
                                     Expression[] arguments) { 
        super(arguments);
        this.prefix = accessPath;
    }


    /**
     *      Super constructor reference.
     *      @param accessPath a reference prefix.
     *      @param arguments an expression mutable list.
     */

    public SuperConstructorReference(ReferencePrefix accessPath,
                                     ImmutableArray<Expression> arguments) { 
        super(arguments);
        this.prefix = accessPath;
    }



    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * @param accessPath a ReferencePrefix of the array reference. 
     *  May contain: 
     * 	several of Expression (as initializers of the array),
     * 	Comments.
     *  Must contain:
     *  execution context
     *  MUST NOT CONTAIN: the ReferencePrefix for the accessPath because
     *    Expression and ReferencePrefix might not be disjunct.
     */ 
    public SuperConstructorReference(ExtList children, 
				     ReferencePrefix accessPath,
				     PositionInfo pi) {
	super(children, pi);	
	this.prefix = accessPath;
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * @param accessPath a ReferencePrefix of the array reference. 
     *  May contain: 
     * 	several of Expression (as initializers of the array),
     * 	Comments.
     *  Must contain:
     *  execution context
     *  MUST NOT CONTAIN: the ReferencePrefix for the accessPath because
     *    Expression and ReferencePrefix might not be disjunct.
     */ 
    public SuperConstructorReference(ExtList children, 
				     ReferencePrefix accessPath) {
	super(children);	
	this.prefix = accessPath;
    }


    /**
     * Get reference prefix.
     * @return the reference prefix.
     */
    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? this : prefix.getFirstElement();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnSuperConstructorReference(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSuperConstructorReference(this);
    }
}
