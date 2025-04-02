/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.ModelException;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;

/**
 * @author Tobias Gutzmann
 */
public class TypeParameterInfo implements TypeParameter, ClassType {
    protected final String name;

    protected final String[] boundNames;

    protected final List<TypeArgumentInfo>[] boundArgs;

    protected final ClassFile containingClassFile;

    /**
     *
     */
    public TypeParameterInfo(String name, String[] boundNames, List<TypeArgumentInfo>[] boundArgs,
            ClassFile containingClassFile) {
        super();
        this.name = name;
        this.boundNames = boundNames;
        this.boundArgs = boundArgs;
        this.containingClassFile = containingClassFile;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ProgramModelElement#getFullName()
     */
    public String getFullName() {
        return Naming.dot(containingClassFile.fullName, name);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ProgramModelElement#getProgramModelInfo()
     */
    public ProgramModelInfo getProgramModelInfo() {
        return containingClassFile.getProgramModelInfo();
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * recoder.abstraction.ProgramModelElement#setProgramModelInfo(recoder.service.ProgramModelInfo)
     */
    public void setProgramModelInfo(ProgramModelInfo pmi) {
        throw new UnsupportedOperationException(
            pmi.getClass().getName() + " should not be set for TypeParamterInfo");
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.NamedModelElement#getName()
     */
    public String getName() {
        return name;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.ModelElement#validate()
     */
    public void validate() throws ModelException {
        // nothing to do
    }

    public String getParameterName() {
        return name;
    }

    public int getBoundCount() {
        return boundNames.length; // never null as java.lang.Object is mandatory
    }

    public String getBoundName(int boundidx) {
        return boundNames[boundidx];
    }

    public List<TypeArgumentInfo> getBoundTypeArguments(int boundidx) {
        return boundArgs[boundidx];
    }

    public boolean equals(Object o) {
        return TypeParameter.EqualsImplementor.equals(this, o);
    }

    /**
     * returns the hash code
     *
     * @return the hashcode
     */
    public int hashCode() {
        return (this.containingClassFile != null ? this.containingClassFile.hashCode() : 10) * 13
                + this.getBoundCount();
    }

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
        return false;
    }

    public boolean isAbstract() {
        return false;
    }

    public List<ClassType> getSupertypes() {
        return containingClassFile.getProgramModelInfo().getSupertypes(this);
    }

    public List<ClassType> getAllSupertypes() {
        return containingClassFile.getProgramModelInfo().getAllSupertypes(this);
    }

    public List<FieldInfo> getFields() {
        return null;
    }

    public List<Field> getAllFields() {
        return null;
    }

    public List<Method> getMethods() {
        return null;
    }

    public List<Method> getAllMethods() {
        return containingClassFile.getProgramModelInfo().getAllMethods(this);
    }

    public List<Constructor> getConstructors() {
        return null;
    }

    public List<ClassType> getAllTypes() {
        return null;
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }

    public boolean isFinal() {
        return false;
    }

    public boolean isStatic() {
        return false;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        // we think this should be ok...
        return true;
    }

    public boolean isStrictFp() {
        return false;
    }

    public ClassType getContainingClassType() {
        return containingClassFile;
    }

    public List<? extends AnnotationUse> getAnnotations() {
        // no annotations possible
        return null;
    }

    public List<ClassType> getTypes() {
        return null;
    }

    public Package getPackage() {
        return containingClassFile.getPackage();
    }

    public ClassTypeContainer getContainer() {
        return containingClassFile;
    }
}
