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

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;


/**
 *  The getTypeReference method returns null - constructors do not have
 *  explicite return types.  A constructor declaration contains its own
 *  name even though it must match the class name: the name occurs as
 *  syntactical element and hence must be represented.
 *  taken from COMPOST and changed to achieve an immutable structure
 */
public class ConstructorDeclaration extends MethodDeclaration implements Constructor {

    /**
     * Constructor declaration.
     * @parm children an ExtList with the children. May
     * include: 
     * 	a TypeReference (as a reference to the return type), 
     * 	a de.uka.ilkd.key.logic.ProgramElementName (as Name of the
     * 		method),
     * 	several ParameterDeclaration (as parameters of the declared
     * 		method), 
     * 	a StatementBlock (as body of the declared method), 
     * 	several Modifier (taken as modifiers of the declaration), 
     * 	a Comment
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * parent is an InterfaceDeclaration      
     */
    public ConstructorDeclaration(ExtList children,
				  boolean parentIsInterfaceDeclaration) {
	super(children, parentIsInterfaceDeclaration, null);	
    }

    
    /**
     * Constructor declaration.
     * @param modifiers a modifier array.
     * @param name an identifier.
     * @param parameters a parameter declaration mutable list.
     * @param exceptions a throws.     
     * @param body a statement block.
     * @param parentIsInterfaceDeclaration a boolean set true iff
     * parent is an InterfaceDeclaration 
     */
    @Deprecated
    public ConstructorDeclaration(Modifier[] modifiers, 
	    			  ProgramElementName name,
				  ParameterDeclaration[] parameters, 
				  Throws exceptions, 
				  StatementBlock body, 
				  boolean parentIsInterfaceDeclaration) { 
	super(modifiers, 
	      null, 
	      name,
	      parameters, 
	      exceptions, 
	      body, 
	      parentIsInterfaceDeclaration);
    }

    
    /**
     * Constructors are never abstract.
     */
    @Override
    public boolean isAbstract() {
        return false;
    }

    
    /**
     * Constructors are never final.
     */
    @Override
    public boolean isFinal() {
        return false;
    }

    
    /**
     * Constructors are never native.
     */
    @Override
    public boolean isNative() {
        return false;
    }

    
    /**
     * Constructors are never static.
     */
    @Override
    public boolean isStatic() {
        return false;
    }

    
    /**
     * Constructors are never strictfp.
     */
    @Override
    public boolean isStrictFp() {
        return false;
    }

    
    /**
     * Constructors are never synchronized.
     */
    @Override
    public boolean isSynchronized() {
        return false;
    }


    @Override    
    public void visit(Visitor v) {
	v.performActionOnConstructorDeclaration(this);
    }
}