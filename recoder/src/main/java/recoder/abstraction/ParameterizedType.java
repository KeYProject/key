/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

import recoder.ModelException;
import recoder.service.ProgramModelInfo;

/**
 * A parameterized type, meaning a generic type plus actual type arguments. All query calls are
 * forwarded to the generic type.
 *
 * @author Tobias Gutzmann
 */
public class ParameterizedType implements ClassType {

    private final ClassType genericType;
    private final List<? extends TypeArgument> typeArgs;

    /**
     *
     */
    public ParameterizedType(ClassType genericType, List<? extends TypeArgument> typeArgs) {
        super();
        if (genericType == null) {
            throw new NullPointerException();
        }
        if (typeArgs == null) {
            throw new NullPointerException();
        }
        this.genericType = genericType;
        this.typeArgs = typeArgs;
    }

    public ClassType getGenericType() {
        return genericType;
    }

    public List<? extends TypeArgument> getTypeArgs() {
        return typeArgs;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ProgramModelElement#getFullName()
     */
    public String getFullName() {
        return genericType.getFullName();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.ProgramModelElement#getProgramModelInfo()
     */
    public ProgramModelInfo getProgramModelInfo() {
        return genericType.getProgramModelInfo();
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * recoder.abstraction.ProgramModelElement#setProgramModelInfo(recoder.service.ProgramModelInfo)
     */
    public void setProgramModelInfo(ProgramModelInfo pmi) {
        throw new UnsupportedOperationException(
            pmi.getClass().getName() + " should not be set for Parameterized Types!");
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.NamedModelElement#getName()
     */
    public String getName() {
        return genericType.getName();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.ModelElement#validate()
     */
    public void validate() throws ModelException {
        // TODO Auto-generated method stub

    }

    public List<? extends TypeParameter> getTypeParameters() {
        return genericType.getTypeParameters();
    }

    public boolean isInterface() {
        return genericType.isInterface();
    }

    public boolean isOrdinaryInterface() {
        return genericType.isOrdinaryInterface();
    }

    public boolean isAnnotationType() {
        return genericType.isAnnotationType();
    }

    public boolean isEnumType() {
        return genericType.isEnumType();
    }

    public boolean isOrdinaryClass() {
        return genericType.isOrdinaryClass();
    }

    public boolean isAbstract() {
        return genericType.isAbstract();
    }

    public List<ClassType> getSupertypes() {
        return genericType.getSupertypes();
    }

    public List<ClassType> getAllSupertypes() {
        return genericType.getAllSupertypes();
    }

    public List<? extends Field> getFields() {
        return genericType.getFields();
    }

    public List<Field> getAllFields() {
        return genericType.getAllFields();
    }

    public List<Method> getMethods() {
        return genericType.getMethods();
    }

    public List<Method> getAllMethods() {
        return genericType.getAllMethods();
    }

    public List<? extends Constructor> getConstructors() {
        return genericType.getConstructors();
    }

    public List<ClassType> getAllTypes() {
        return genericType.getAllTypes();
    }

    public boolean isFinal() {
        return genericType.isFinal();
    }

    public boolean isStatic() {
        return genericType.isStatic();
    }

    public boolean isPrivate() {
        return genericType.isPrivate();
    }

    public boolean isProtected() {
        return genericType.isProtected();
    }

    public boolean isPublic() {
        return genericType.isPublic();
    }

    public boolean isStrictFp() {
        return genericType.isStrictFp();
    }

    public ClassType getContainingClassType() {
        return genericType.getContainingClassType();
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return genericType.getAnnotations();
    }

    public List<? extends ClassType> getTypes() {
        return genericType.getTypes();
    }

    public Package getPackage() {
        return genericType.getPackage();
    }

    public ClassTypeContainer getContainer() {
        return genericType.getContainer();
    }

}
