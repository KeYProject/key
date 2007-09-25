// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Type declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */
public abstract class TypeDeclaration extends JavaDeclaration
 implements NamedProgramElement, MemberDeclaration,
    TypeDeclarationContainer, ClassType, VariableScope, TypeScope {

    /**
     *      Name.
     */

    protected final ProgramElementName name;

    /**
     *      Full name.
     */
    protected final ProgramElementName fullName;

    /**
     *      Members.
     */
    protected final ArrayOfMemberDeclaration members;

    protected final boolean parentIsInterfaceDeclaration;

    protected final boolean isLibrary;

    /**
     *      Type declaration.
     */

    public TypeDeclaration() {
	this.name    = null;
	this.fullName    = null;
	this.members = null;
	this.parentIsInterfaceDeclaration = false;
	this.isLibrary = false;
    }

    /**
     *      Type declaration.     
     *      @param mods a modifier array.
     *      @param name ProgramElementName of the type
     *      @param members an array containing the memberdeclarations of
     * this type
     */

    public TypeDeclaration(Modifier[] mods, ProgramElementName name,
			   ProgramElementName fullName,
			   MemberDeclaration[] members, boolean
			   parentIsInterfaceDeclaration, boolean isLibrary) {  
	super(mods);
	this.name    = name;
	this.fullName = fullName;
	this.members = new ArrayOfMemberDeclaration(members);
	this.parentIsInterfaceDeclaration = parentIsInterfaceDeclaration;
	this.isLibrary = isLibrary;
    }

    /**
     * @param children an ExtList of children. 
     * @param name the ProgramElementName of the type
     * May contain: 
     *   several MemberDeclaration (as members of the type),
     *   a parentIsInterfaceDeclaration (indicating if parent is interface),
     *   several Modifier (as modifiers of the type decl),
     *   Comments
     */
    public TypeDeclaration(ExtList children, ProgramElementName name, 
			   ProgramElementName fullName,
			   boolean isLibrary) {
	super(children);
	this.name = name;
	this.fullName = fullName;
	this.members = new ArrayOfMemberDeclaration
	    ((MemberDeclaration[])children.collect(MemberDeclaration.class));
	ParentIsInterfaceDeclaration piid=(ParentIsInterfaceDeclaration)
	    children.get(ParentIsInterfaceDeclaration.class);
	if (piid!=null) {
	    this.parentIsInterfaceDeclaration =(piid).getValue();
	} else {
	    this.parentIsInterfaceDeclaration =false; 
	}
	this.isLibrary = isLibrary;
    }

    /**
     * @param children an ExtList of children. 
     * May contain: 
     *   a ProgramElementName (as name),
     *   several MemberDeclaration (as members of the type),
     *   a parentIsInterfaceDeclaration (indicating if parent is interface),
     *   several Modifier (as modifiers of the type decl),
     *   Comments
     */
    public TypeDeclaration(ExtList children, ProgramElementName fullName,
			   boolean isLibrary) {
	this(children, 
	     (ProgramElementName)children.get(ProgramElementName.class), 
	     fullName, isLibrary);
    }

    public SourceElement getFirstElement() {
        if (modArray != null && (modArray.size()>0)) {
            return modArray.getModifier(0);
        } else {
            return this;
        }
    }

    public SourceElement getLastElement() {
        // end of member block
        return this;
    }

    /**
 *      Get name.
 *      @return the string.
     */

    public final String getName() {
        return (name == null) ? ((fullName == null) ? null : fullName.toString()) 
	: name.toString();
    }

    public String getFullName() {
	return (fullName == null) ? getName() : fullName.toString();
    }

    /** 
     * returns the default value of the given type 
     * according to JLS 4.5.5
     * @return the default value of the given type 
     * according to JLS 4.5.5
     */
    public Literal getDefaultValue() {
	return NullLiteral.NULL;
    }

    /**
 *      Get ProgramElementName.
 *      @return the ProgramElementName.
     */

    public ProgramElementName getProgramElementName() {
        return name;
    }


    /**
     * Get members.
     * @return the member declaration array.
     */

    public ArrayOfMemberDeclaration getMembers() {
        return members;
    }

    public boolean isLibraryClass() {
	return isLibrary;
    }

    /** TO BE IMPLEMENTED
     */
    public de.uka.ilkd.key.java.abstraction.Package getPackage(Services s) {
       System.err.println("Method in class TypeDeclaration not implemented." );
       return null;
    }

    /** 
     * returns the local declared supertypes
     */
    public abstract ListOfKeYJavaType getSupertypes();

    /** 
     * TO BE IMPLEMENTED
     */
    public ListOfClassType getAllSupertypes(Services services) {
	System.err.println("Method in class TypeDeclaration not implemented." );     
	return null;
    }

    /** TO BE IMPLEMENTED
     */
    public ListOfField getFields(Services services) {
	System.err.println("Method in class TypeDeclaration not implemented." );   
	return null;
    }

    /** TO BE IMPLEMENTED
     */
    public ListOfField getAllFields(Services services) {
       	System.err.println("Method in class TypeDeclaration not implemented." );
	return null;
    }

    /** TO BE IMPLEMENTED
     */
    public ListOfMethod getMethods(Services services) {     
	System.err.println("Method in class TypeDeclaration not implemented." );
	return null;
    }


    /** TO BE IMPLEMENTED
     */
    public ListOfMethod getAllMethods(Services services) {
	System.err.println("Method in class TypeDeclaration not implemented." );
	return null;
    }

    /** TO BE IMPLEMENTED
     */
    public ListOfConstructor getConstructors(Services services) {
      	System.err.println("Method in class TypeDeclaration not implemented." );
	return null;
    }

    /** TO BE IMPLEMENTED
     */
    public ListOfClassType getTypes(Services services) {
	System.err.println("Method in class TypeDeclaration not implemented." );
	return null;
    }

    /** TO BE IMPLEMENTED
     */
    public ListOfClassType getAllTypes(Services services) {
	System.err.println("Method in class TypeDeclaration not implemented." );
	return null;
    }


    /**
     *      Get the number of type declarations in this container.
     *      @return the number of type declarations.
     */

    public int getTypeDeclarationCount() {
        int count = 0;
        if (members != null) {
            for (int i = members.size() - 1; i >= 0; i -= 1) {
                if (members.getMemberDeclaration(i) instanceof TypeDeclaration) {
                    count += 1;
                }
            }
        }
        return count;
    }

    /*
      Return the type declaration at the specified index in this node's
      "virtual" type declaration array.
      @param index an index for a type declaration.
      @return the type declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (members != null) {
            int s = members.size();
            for (int i = 0; i < s && index >= 0; i += 1) {
                MemberDeclaration md = members.getMemberDeclaration(i);
                if (md instanceof TypeDeclaration) {
                    if (index == 0) {
                        return (TypeDeclaration)md;
                    }
                    index -= 1;
                }
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Test whether the declaration is final.
     */

    public boolean isFinal() {
        return super.isFinal();
    }

    /**
     * Test whether the declaration is private.
     */

    public boolean isPrivate() {
        return super.isPrivate();
    }

    /**
     * Test whether the declaration is protected.
     */

    public boolean isProtected() {
        return super.isProtected();
    }

    /**
     * Test whether the declaration is public.
     */

    public boolean isPublic() {
        return parentIsInterfaceDeclaration || super.isPublic();
    }

    /**
     * Test whether the declaration is static.
     */

    public boolean isStatic() {
        return parentIsInterfaceDeclaration || super.isStatic();
    }

    /**
     * Test whether the declaration is strictfp.
     */

    public boolean isStrictFp() {
        return super.isStrictFp();
    }

    /**
     * Test whether the declaration is abstract.
     */

    public boolean isAbstract() {
        return super.isAbstract();
    }

}
