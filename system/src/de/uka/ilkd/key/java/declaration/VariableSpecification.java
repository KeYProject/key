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



package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.abstraction.Variable;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/**
 *    Variable specification that defines a variable name. This is a part of a
 *    {@link recoder.java.declaration.VariableDeclaration} and does not
 *    contain a type reference or own modifiers. Note that calls to modifiers
 *    are delegated to the enclosing variable declaration and are therefore
 *    discouraged. This was necessary to subtype Declaration as analyses are
 *    interested in the exact location of a variable name.
 *    
 *    @author AL
 */

public class VariableSpecification extends JavaNonTerminalProgramElement
    implements NamedProgramElement, ExpressionContainer, Variable//,Declaration
 {

     private int hashcode=0; // just cache, does not break immutability
       
     /**
      *	Initializer.
      */     
     protected final Expression initializer;
     
     /**
      * Dimensions.
      */
     protected final int dimensions;

     /** the type 
      */
     protected final Type type;

     protected final IProgramVariable var;

     public VariableSpecification() {
	 this(null, 0, null, null, null);
     }

     public VariableSpecification(IProgramVariable var) {
	 this(var, var.getKeYJavaType());
     }

     public VariableSpecification(IProgramVariable var, Type type) {
	 this(var, 0, null, type, null);
     }


     public VariableSpecification(IProgramVariable var, Expression init, 
				  Type type) {
	 this(var, 0, init, type, null);
     }
     
     public VariableSpecification(IProgramVariable var, int dim, 
             Expression init, Type type) {
         this(var, dim, init, type, PositionInfo.UNDEFINED);
     }
     
     public VariableSpecification(IProgramVariable var, int dim, 
				  Expression init, Type type, PositionInfo pi) {
	 super(pi);
	 this.var    = var;
	 this.initializer = init;
	 this.dimensions  = dim;
	 this.type   = type;
     }
     

    /**
     * Constructor for the transformation of RECODER ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * 	May contain:
     * 		an Expression (as initializer of the variable)
     * 		a Comment
     * @param dim the dimension of this type
     */
     public VariableSpecification(ExtList children, IProgramVariable var, 
				  int dim, Type type) {
	super(children);
	this.var    = var;
	initializer = children.get(Expression.class);
	dimensions  = dim;
	this.type   = type;
    }


    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (var        != null) result++;
        if (initializer != null) result++;
        return result;
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
        if (var != null) {
            if (index == 0) return var;
            index--;
        }
        if (initializer != null) {
            if (index == 0) return initializer;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */

    public int getExpressionCount() {
        return (initializer != null) ? 1 : 0;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Expression getExpressionAt(int index) {
        if (initializer != null && index == 0) {
            return initializer;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get name.
     *      @return the string.
     */
    public final String getName() {
        return (var == null) ? null : var.name().toString();
    }

    /**
     *      Get name.
     *      @return the name.
     */
    public ProgramElementName getProgramElementName() {
	if (var.name() instanceof ProgramElementName) {
	    return (ProgramElementName) var.name();
	} else {
	    return new ProgramElementName(var.name().toString()); //only with SVs
	}
    }


    /**
     *      Get program variable
     *      @return the program variable.
     */
    public IProgramVariable getProgramVariable() {
	return var;
    }



    /**
     *      Get dimensions.
     *      @return the int value.
     */
    public int getDimensions() {
        return dimensions;
    }

    /**
     *      Get initializer.
     *      @return the expression.
     */
    public Expression getInitializer() {
        return initializer;
    }
    
    
    public boolean hasInitializer() {
        return initializer!=null;
    }

     public boolean isFinal() {   
         System.out.println("Method in Variable Specification not implemented!");
     	 return false;
     }


     public Type getType() {
	 return type;
     }

    public String getFullName() {
        return getName();
    }

    public SourceElement getFirstElement() {
        return var;
    }

    public SourceElement getLastElement() {
        if (initializer != null) {
            return initializer.getLastElement();
        } else {
            return var;
        }
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnVariableSpecification(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printVariableSpecification(this);
    }

    /** equals modulo renaming is described in the corresponding
     * comment in class SourceElement. The variables declared in the
     * local variable declaration have to be added to the
     * NameAbstractionTable.
     */
     public boolean equalsModRenaming(SourceElement se, 
				     NameAbstractionTable nat) {
	if (!(se instanceof VariableSpecification)) {
	    return false;
	}		 
	final VariableSpecification vs = (VariableSpecification)se;
	if (dimensions != vs.getDimensions()) {
	    return false;
	}
	if (type!=null) {
	    if (!(type.equals(vs.getType()))) {
		return false;
	    }
	} else {
	    if (vs.getType()!=null) {
		return false;
	    }
	}
	nat.add(var, vs.getProgramVariable());	
        if (vs.getChildCount()!=getChildCount()) {
	    return false;
	}	
	for (int i = 0, cc = getChildCount(); i<cc; i++) {
	    if (!getChildAt(i).equalsModRenaming
		(vs.getChildAt(i), nat)) {
		return false;
	    }
	}
	return true;	
    }
     
    public int hashCode(){
	if (hashcode!=0) return hashcode;
    	int result = 17;
    	result = 37 * result + dimensions;
    	result = 37 * result + ((type==null) ? 0 : type.hashCode());
    	result = 37 * result + getChildCount();
    	for (int i = 0, cc = getChildCount(); i<cc; i++) {
    		result = 37 * result + getChildAt(i).hashCode();
    	}
    	return hashcode=result;
    }
     
    public boolean equals (Object o){
    	return super.equals(o);
    }
    
    public MatchConditions match(SourceData source, MatchConditions matchCond) {        
        final ProgramElement pe = source.getSource();
        matchCond = super.match(source, matchCond);
        if (matchCond != null) {
            if (getDimensions() != ((VariableSpecification)pe).getDimensions()) {
                Debug.out("Program match. Variables have different dimension " +
                                "(template, source)", this, pe);
                return null;
            }
        }
        return matchCond;
    }
}
