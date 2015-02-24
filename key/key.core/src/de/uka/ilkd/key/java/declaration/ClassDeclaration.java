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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;

/**
 *  There are several types of class declarations:
 *  <ul>
 *  <li>package-less outer classes
 *  <ul>
 *  <li>getClassContainer() == null
 *  <li>getStatementContainer() == null
 *  <li>getName() != null
 *  </ul>
 *  <li>ordinary outer classes
 *  <ul>
 *  <li>getClassContainer() instanceof Package
 *  <li>getStatementContainer() == null
 *  <li>getName() != null
 *  </ul>
 *  <li>member classes
 *  <ul>
 *  <li>getClassContainer() instanceof ClassDeclaration
 *  <li>getStatementContainer() == null
 *  <li>getName() != null
 *  </ul>
 *  <li>local class
 *  <ul>
 *  <li>getClassContainer() == null
 *  <li>getStatementContainer() != null
 *  <li>getName() != null
 *  </ul>
 *  <li>local anonymous class
 *  <ul>
 *  <li>getClassContainer() == null
 *  <li>getStatementContainer() instanceof expression.New
 *  <li>getName() == null
 *  </ul>
 *  </ul>
 *  Anonymous local classes have exactly one supertype and no
 *  subtypes.
 *  <BR>
 *  Binary classes may have only binary members.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public class ClassDeclaration extends TypeDeclaration implements Statement {
    
    protected final Extends extending;

    protected final Implements implementing;
    
    protected final boolean isInnerClass;
    
    protected final boolean isLocalClass;
    
    protected final boolean isAnonymousClass;

    /**
     * Class declaration.     
     * @param mods a modifier array.
     * @param name Identifier of the class
     * @param members an array containing the memberdeclarations of
     * this type
     * @param implemented of type Implement containing the
     * interfaces implemented by this class
     * @param extended Extend containing the class extended by
     * the class of this classdeclaration
     * @param parentIsInterfaceDeclaration boolean true iff
     * parent is an InterfaceDeclaration 
     */
    public ClassDeclaration(Modifier[] mods, 
	    		    ProgramElementName name,
			    Extends extended, 
			    ProgramElementName fullName, 
			    Implements implemented,
			    MemberDeclaration[] members, 
			    boolean parentIsInterfaceDeclaration, 
			    boolean isLibrary) {
	super(mods,
	      name,
	      fullName,
	      members,
	      parentIsInterfaceDeclaration, 
	      isLibrary);
	this.extending    = extended;
	this.implementing = implemented;
	this.isInnerClass = false;
	this.isAnonymousClass = false;
	this.isLocalClass = false;
    }

    /**
     * uses children list to create non-anonymous class 
     * @param children the ExtList with all children building up this
     *  class declaration
     * May contain: a Extends (as pointer to a
     * class), a Implements (as pointer to an interface)
     * ProgramElementName (as name), several MemberDeclaration (as members of
     * the type), a parentIsInterfaceDeclaration (indicating if parent is
     * interface), several Modifier (as modifiers of the type decl), a Comment
     * @param fullName the fully qualified ProgramElementName of this class
     * @param isLibrary a boolean flag indicating if this class represents a 
     * library class (such classes have usually no method implementations but 
     * specifications)      
     */
    public ClassDeclaration(ExtList children, 
	    		    ProgramElementName fullName, 
			    boolean isLibrary, 
			    boolean innerClass, 
			    boolean anonymousClass,
			    boolean localClass) { 
	super(children, fullName, isLibrary);
	extending=children.get(Extends.class);
	implementing=children.get(Implements.class);
	this.isInnerClass = innerClass;
	this.isAnonymousClass = anonymousClass;
	this.isLocalClass =localClass;
    } 
    
    public ClassDeclaration(ExtList children, 
	    		    ProgramElementName fullName, 
	    		    boolean isLibrary) { 
        this(children, fullName, isLibrary, false, false, false);
    } 


    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if(modArray != null) result += modArray.size();
        if(name != null) result++;
        if(extending != null) result++;
        if(implementing != null) result++;
        if(members != null) result += members.size();
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *            of bounds
     */
    public ProgramElement getChildAt(int index) {
        int len;
        if (modArray != null) {
            len = modArray.size();
            if (len > index) {
                return modArray.get(index);
            }
            index -= len;
        }
        if (name != null) {
            if (index == 0) return name;
            index--;
        }
        if (extending != null) {
            if (index == 0) return extending;
            index--;
        }
        if (implementing != null) {
            if (index == 0) return implementing;
            index--;
        }
        if (members != null) {
            return members.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    
    /**
     * Get extended types.
     * @return the extends.
     */
    public Extends getExtendedTypes() {
        return extending;
    }

    /**
     * Get implemented types.
     * @return the implements.
     */
    public Implements getImplementedTypes() {
        return implementing;
    }

    /**
     * Classes are never strictfp.
     */
    public boolean isStrictFp() {
        return false;
    }

    /**
     * Classes are never transient.
     */
    public boolean isTransient() {
        return false;
    }
    
    public boolean isInnerClass(){
        return isInnerClass;
    }
    
    public boolean isAnonymousClass(){
        return isAnonymousClass;
    }
    
    public boolean isLocalClass(){
        return isLocalClass;
    }

    /**
     * Classes are never volatile.
     */
    public boolean isVolatile() {
        return false;
    }

    public boolean isInterface() {
        return false;
    }
    
    /** 
     * returns the local declared supertypes
     */
    public ImmutableList<KeYJavaType> getSupertypes() {
	ImmutableList<KeYJavaType> types = ImmutableSLList.<KeYJavaType>nil();
	if (implementing != null) {
	    for (int i = implementing.getTypeReferenceCount()-1; i>=0; i--) {
		types = types.prepend(implementing.getTypeReferenceAt(i).
				      getKeYJavaType());
	    }
	}
	if (extending != null) {
	    types = types.prepend
		(extending.getTypeReferenceAt(0).getKeYJavaType());
	}
	return types;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnClassDeclaration(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printClassDeclaration(this);
    }
}