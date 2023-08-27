/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

import recoder.service.ProgramModelInfo;

/**
 * A program model element representing the null type.
 *
 * @author AL
 * @author RN
 */
public class NullType implements ClassType {

    /**
     * The name of this type.
     */
    public static final String NULL = "null";

    private ProgramModelInfo pmi;

    /**
     * Create a new null type for the given program model info.
     *
     * @param info the program model info responsible for this type.
     */
    public NullType(ProgramModelInfo info) {
        this.pmi = info;
    }

    /**
     * Returns the name of this element.
     *
     * @return <CODE>"null"</CODE>.
     */
    public String getName() {
        return NULL;
    }

    /**
     * Returns the name of this element.
     *
     * @return <CODE>"null"</CODE>.
     */
    public String getFullName() {
        return NULL;
    }

    /**
     * Returns the instance that can retrieve information about this program model element.
     *
     * @return the program model info of this element.
     */
    public ProgramModelInfo getProgramModelInfo() {
        return pmi;
    }

    /**
     * Sets the instance that can retrieve information about this program model element.
     *
     * @param info the program model info for this element.
     */
    public void setProgramModelInfo(ProgramModelInfo info) {
        pmi = info;
    }

    public void validate() {
        // always valid
    }

    /**
     * Checks if this member is final.
     *
     * @return <CODE>true</CODE>.
     */
    public boolean isFinal() {
        return true;
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
        return false;
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
     * @return <CODE>true</CODE>.
     */
    public boolean isPublic() {
        return true;
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
     * Returns the (empty) list of class types locally defined within this container.
     *
     * @return an empty list of contained class types.
     */
    public List<? extends ClassType> getTypes() {
        return pmi.getTypes(this);
    }

    /**
     * Returns all class types that are inner types of this class type.
     *
     * @return an empty list of class types.
     */
    public List<ClassType> getAllTypes() {
        return pmi.getAllTypes(this);
    }

    /**
     * Returns the logical parent class of this member.
     *
     * @return the class type containing this member.
     */
    public ClassType getContainingClassType() {
        return pmi.getContainingClassType(this);
    }

    /**
     * Returns the enclosing package or class type, or method.
     *
     * @return <CODE>null</CODE>.
     */
    public ClassTypeContainer getContainer() {
        return pmi.getClassTypeContainer(this);
    }

    /**
     * Checks if this class type denotes an interface.
     *
     * @return <CODE>false</CODE>.
     */
    public boolean isInterface() {
        return false;
    }

    public boolean isOrdinaryInterface() {
        return false;
    }

    public boolean isAnnotationType() {
        return false;
    }

    public boolean isEnumType() {
        return false;
    }

    public boolean isOrdinaryClass() {
        return true;
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
     * Returns the list of locally declared supertypes of this class type.
     *
     * @return the empty list of supertypes of this type.
     */
    public List<ClassType> getSupertypes() {
        return pmi.getSupertypes(this);
    }

    /**
     * Returns the list of all supertypes of this class type, including this type.
     *
     * @return a list with this element as single member.
     */
    public List<ClassType> getAllSupertypes() {
        return pmi.getAllSupertypes(this);
    }

    /**
     * Returns the fields locally defined within this class type.
     *
     * @return the (empty) list of field members of this type.
     */
    public List<? extends Field> getFields() {
        return pmi.getFields(this);
    }

    /**
     * Returns all visible fields that are defined in this class type or any of its supertypes.
     *
     * @return the (empty) list of visible field members of this type.
     */
    public List<Field> getAllFields() {
        return pmi.getAllFields(this);
    }

    /**
     * Returns the methods locally defined within this class type.
     *
     * @return the (empty) list of methods of this type.
     */
    public List<Method> getMethods() {
        return pmi.getMethods(this);
    }

    /**
     * Returns the constructors locally defined within this class type.
     *
     * @return the (empty) list of constructors of this type.
     */
    public List<? extends Constructor> getConstructors() {
        return pmi.getConstructors(this);
    }

    /**
     * Returns all visible methods that are defined in this class type or any of its supertypes.
     *
     * @return the (empty) list of visible methods of this type.
     */
    public List<Method> getAllMethods() {
        return pmi.getAllMethods(this);
    }

    /**
     * Returns the package this element is defined in.
     *
     * @return <CODE>null</CODE>.
     */
    public Package getPackage() {
        return pmi.getPackage(this);
    }

    /**
     * returns <code>null</code>
     */
    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }
}
