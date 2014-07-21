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

package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Type operator.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class TypeOperator extends Operator implements TypeReferenceContainer {

    /**
     *      Type reference.
     */
    protected final TypeReference typeReference;


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * 	May contain:
     *          a TypeReference (the referred type)
     * 		2 of Expression (the first Expression as left hand
     * 			side, the second as right hand side), 
     * 		Comments
     */
    public TypeOperator(ExtList children) {
	super(children);
	typeReference=children.get(TypeReference.class);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * 	May contain:
     *          a TypeReference (the referred type)
     * 		2 of Expression (the first Expression as left hand
     * 			side, the second as right hand side), 
     * 		Comments
     */
    public TypeOperator(ExtList children, PositionInfo pi) {
	super(children);
	typeReference=children.get(TypeReference.class);
    }
    
    public TypeOperator(Expression unaryChild, TypeReference typeref) {
        super(unaryChild);
        typeReference=typeref;
    }

    public TypeOperator(Expression[] arguments, TypeReference typeref) {
        super(arguments);
        typeReference=typeref;
    }

    public TypeOperator(){
	typeReference=null;
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (typeReference != null) ? 1 : 0;
    }

    /*
      Return the type reference at the specified index in this node's
      "virtual" type reference array.
      @param index an index for a type reference.
      @return the type reference with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public TypeReference getTypeReferenceAt(int index) {
        if (typeReference != null && index == 0) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get type reference.
     *      @return the type reference.
     */
    public TypeReference getTypeReference() {
        return typeReference;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, 
				      ExecutionContext ec) {
	return getKeYJavaType(javaServ);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return getTypeReference().getKeYJavaType();
    }



}