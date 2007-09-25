// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.kit.TwoPassTransformation;
import recoder.list.CompilationUnitMutableList;
import de.uka.ilkd.key.util.Debug;

/**
 * The Java DL requires some implicit fields, that are available in each
 * Java class. The name of the implicit fields is usually enclosed
 * between two angle brackets. 
 * Two access the fields in a uniform way, they are added as usual
 * fields to the classes, in particular this allows us to parse them in
 * more easier.
 *   For further information see also
 *   <ul>
 *     <li> {@link ImplicitFieldAdder} </li>
 *     <li> {@link CreateObjectBuilder}  </li>
 *     <li> {@link PrepareObjectBuilder} </li>
 *   </ul>
 */
public abstract class RecoderModelTransformer extends TwoPassTransformation {

    protected CrossReferenceServiceConfiguration services;
    protected CompilationUnitMutableList units;

    /**
     * creates a transormder for the recoder model
     * @param services the CrossReferenceServiceConfiguration to access
     * model information 
     * @param units the array of CompilationUnits describing the model 
     * to be transformed 
     */
    public RecoderModelTransformer
	(CrossReferenceServiceConfiguration services, 
	 CompilationUnitMutableList units) {	
	super(services);
	this.services = services;
	this.units = units;
    }

    /** 
     * returns the default value of the given type 
     * according to JLS Sect. 4.5.5
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
     */
    public Expression getDefaultValue(Type type) {
	if (type instanceof ClassType || type instanceof ArrayType) {
	    return new NullLiteral();
	} else if (type instanceof PrimitiveType) {
	    if ("boolean".equals(type.getName())) {
		return new BooleanLiteral(false);
	    } else if ("byte".equals(type.getName())  ||
		       "short".equals(type.getName()) || 
		       "int".equals(type.getName())) {
		return new IntLiteral(0);
	    } else if ("long".equals(type.getName())) {
		return new LongLiteral(0);
	    } else if ("char".equals(type.getName())) {
		return new CharLiteral((char)0);
	    } else if ("float".equals(type.getName())) {
		return new FloatLiteral(0.0F);
	    } else if ("double".equals(type.getName())) {
		return new DoubleLiteral(0.0D);
	    }
	}
	Debug.fail("makeImplicitMembersExplicit: unknown primitive type"+type);
	return null;
    }
    
    /** 
     * attaches a method declaration to the declaration of type td at
     * position idx
     * @param md the MethodDeclaration to insert
     * @param td the TypeDeclaration that becomes parent of the new
     * method
     * @param idx the position where to add the method
     */
    public void attach(MethodDeclaration md, TypeDeclaration td, 
		       int idx) {
	super.attach(md, td, idx);
    }

    /**
     * returns if changes have to be reported to the change history
     * @return true, iff changes have to be reported to the change history
     */
    public boolean isVisible() {
	return true;
    }
    
    /**
     * The method is called for each type declaration of the compilation
     * unit and initiates the syntactical transformation. If you want to
     * descend in inner classes you have to implement the recusrsion by
     * yourself.
     */
    protected abstract void makeExplicit(TypeDeclaration td);

    // Java construction helper methods for recoder data structures

    protected FieldReference attribute
	(ReferencePrefix prefix, Identifier attributeName) {
	return new FieldReference(prefix, attributeName);
    }


    protected CopyAssignment assign(Expression lhs, Expression rhs) {
	return new CopyAssignment(lhs, rhs);
    }

    protected LocalVariableDeclaration declare
	(String name, ClassType type) {
	return new LocalVariableDeclaration
	    (new TypeReference(new Identifier(type.getName())), 
	     new Identifier(name));
    }

    protected LocalVariableDeclaration declare
	(String name, TypeDeclaration type) {
	return new LocalVariableDeclaration
	    (new TypeReference
	     ((Identifier)type.getIdentifier().deepClone()), 
	     new Identifier(name));
    }


    /**
     * invokes model transformation for each top level type declaration
     * in any compilation unit. <emph>Not</emph> for inner classes.
     */
    public void makeExplicit() {
	for (int i = 0; i<units.size(); i++) {
	    CompilationUnit unit = units.getCompilationUnit(i);
	    int typeCount = unit.getTypeDeclarationCount();
	    for (int j = 0; j<typeCount; j++) {
		makeExplicit(unit.getTypeDeclarationAt(j));
	    }
	}
    }

    /**
     * Starts the transformation. 
     */
    public void transform() {
	super.transform();
	makeExplicit();
    }

}
