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

package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.util.ExtList;

/**
   Default constructor of class types.
   @deprecated is actually never used
 */
@Deprecated
public class DefaultConstructor implements Constructor {

    protected final String name;
    protected final boolean parentIsPublic;


    //???use ProgramElementName instead of name?????
    public DefaultConstructor(ExtList children) {
	name=children.get(String.class);
	parentIsPublic=children.get(Boolean.class).booleanValue();
    }

    /**
       Create a new default constructor for the given class type.
       The name of the constructor is set appropriately.
       @param name of the Constructor
       @param parentIsPublic is set true iff the parent is declared public.
     */
    @Deprecated
    public DefaultConstructor(String name, boolean parentIsPublic) {
	this.parentIsPublic = parentIsPublic;
	this.name=name;
    }
    
    /**
       Checks if this member is final.
       @return <CODE>false</CODE>.
     */
    public boolean isFinal() {
	return false;
    }
    
    /**
       Checks if this member is static.
       @return <CODE>true</CODE>.
     */
    public boolean isStatic() {
	return true;
    }
    
    /**
       Checks if this member is private.
       @return <CODE>false</CODE>.
     */
    public boolean isPrivate() {
	return false;
    }
    
    /**
       Checks if this member is protected.
       @return <CODE>false</CODE>.
     */
    public boolean isProtected() {
	return false;
    }
    
    /**
       Checks if this member is public.
       @return <CODE>true</CODE>, if the containing class type is public,
       <CODE>false</CODE> otherwise.
     */
    public boolean isPublic() {
	return parentIsPublic;
	// else, it is package visible
    }
    
    /**
       Checks if this member is protected.
       @return <CODE>false</CODE>.
     */
    public boolean isStrictFp() {
	return false;
    }

    /**
       Checks if this member is abstract.
       @return <CODE>false</CODE>.
     */
    public boolean isAbstract() {
	return false;
    }

    /**
       Checks if this member is native.
       @return <CODE>false</CODE>.
     */
    public boolean isNative() {
	return false;
    }
    
    /**
       Checks if this member is synchronized.
       @return <CODE>false</CODE>.
     */
    public boolean isSynchronized() {
	return false;
    }
    
    /**  TO BE IMPLEMENTED
	Returns the signature of this constructor.
	@return the signature of this constructor.
    */
    public Type[] getSignature(){
	return new Type[0];
    }

    /** 
        Returns the return type of this method.
        @return the return type of this method.
    */    
    public Type getReturnType() {
        return null;
    }

    /** 
        Returns the (empty) exception list of this constructor.
        @return the (empty) exception list of this constructor.
    */    
    public ClassType[] getExceptions() {
        return new ClassType[0];
    }

    /** TO BE IMPLEMENTED
       Returns the package this element is defined in.
       @return the package of this element.
     */
    public Package getPackage() {
        return null;
    }

    /** TO BE IMPLEMENTED
        Returns the (empty) list of class types locally defined within this
        container.
        @return a list of contained class types.
    */
    public ClassType[] getTypes() {
        return new ClassType[0];
    }

    /**
       Returns the name of this element.
       @return the name of this element.
     */
    public String getName() {
        return name;
    }
    
    /**
       Returns the name of this element.
       @return the name of this element.
     */
    public String getFullName() {
        return name;
    }
}