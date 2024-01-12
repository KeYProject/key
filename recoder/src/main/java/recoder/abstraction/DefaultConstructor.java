/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

import recoder.ModelException;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

/**
 * Default constructor of class types.
 *
 * @author AL
 */
public class DefaultConstructor implements Constructor {

    protected ProgramModelInfo service;

    protected final ClassType ownerClass;

    /**
     * Create a new default constructor for the given class type. The name of the constructor is set
     * appropriately.
     *
     * @param ownerClass the owner class of this constructor.
     */
    public DefaultConstructor(ClassType ownerClass) {
        Debug.assertNonnull(ownerClass);
        this.ownerClass = ownerClass;
    }

    /**
     * Returns the instance that can retrieve information about this program model element.
     *
     * @return the program model info of this element.
     */
    public ProgramModelInfo getProgramModelInfo() {
        return service;
    }

    /**
     * Sets the instance that can retrieve information about this program model element.
     *
     * @param service the program model info for this element.
     */
    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public void validate() throws ModelException {
        // always valid
    }

    /**
     * Checks if this member is final.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isFinal() {
        return false;
    }

    /**
     * Checks if this member is static.
     *
     * @return <CODE>true</CODE>.
     */
    public boolean isStatic() {
        return true;
    }

    /**
     * Checks if this member is private.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isPrivate() {
        return getContainingClassType().isEnumType();
    }

    /**
     * Checks if this member is protected.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isProtected() {
        return false;
    }

    /**
     * Checks if this member is public.
     *
     * @return <CODE>true</CODE>, if the containing class type is public, <CODE>false</CODE>
     *         otherwise.
     */
    public boolean isPublic() {
        return getContainingClassType().isPublic() && !getContainingClassType().isEnumType();
        // else, it is package or private visible, depending on type
    }

    /**
     * Checks if this member is strictfp.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isStrictFp() {
        return false;
    }

    /**
     * Checks if this member is abstract.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isAbstract() {
        return false;
    }

    /**
     * Checks if this member is native.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isNative() {
        return false;
    }

    /**
     * Checks if this member is synchronized.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isSynchronized() {
        return false;
    }

    /**
     * Returns the logical parent class of this member.
     *
     * @return the class type containing this member.
     * @see recoder.service.ProgramModelInfo#getContainingClassType
     */
    public ClassType getContainingClassType() {
        return ownerClass;
    }

    /**
     * Returns the return type of this method.
     *
     * @return the return type of this method.
     */
    public Type getReturnType() {
        return service.getReturnType(this);
    }

    /**
     * Returns the (empty) signature of this constructor.
     *
     * @return the (empty) signature of this constructor.
     */
    public List<Type> getSignature() {
        return service.getSignature(this);
    }

    /**
     * Returns the (empty) exception list of this constructor.
     *
     * @return the (empty) exception list of this constructor.
     */
    public List<ClassType> getExceptions() {
        return service.getExceptions(this);
    }

    /**
     * Returns the enclosing class type.
     *
     * @return the container of this element.
     */
    public ClassTypeContainer getContainer() {
        return getContainingClassType();
    }

    /**
     * Returns the package this element is defined in.
     *
     * @return the package of this element.
     */
    public Package getPackage() {
        return service.getPackage(this);
    }

    /**
     * Returns the (empty) list of class types locally defined within this container.
     *
     * @return a list of contained class types.
     */
    public List<? extends ClassType> getTypes() {
        return service.getTypes(this);
    }

    /**
     * Returns the name of this element.
     *
     * @return the name of this element.
     */
    public String getName() {
        return getContainingClassType().getName();
    }

    /**
     * Returns the maximal expanded name including all applicable qualifiers.
     *
     * @return the full name of this program model element.
     */
    public String getFullName() {
        return Naming.getFullName(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.Method#isVarArgMethod()
     */
    public boolean isVarArgMethod() {
        // no arguments at all
        return false;
    }

    /**
     * @return <code>null</code>
     */
    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public DefaultConstructor deepClone() {
        throw new UnsupportedOperationException("Cannot deep-clone default constructor");
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }


}
