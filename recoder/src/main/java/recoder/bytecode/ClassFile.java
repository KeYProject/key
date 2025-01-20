/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.*;
import recoder.abstraction.Package;

public class ClassFile extends ByteCodeElement implements ClassType {

    String location;

    String fullName;

    String physicalName;

    String superName;

    String[] interfaceNames;

    List<FieldInfo> fields;

    List<MethodInfo> methods;

    List<ConstructorInfo> constructors;

    List<AnnotationUseInfo> annotations;

    List<TypeParameterInfo> typeParams;

    String[] innerClasses;

    List<TypeArgumentInfo> superClassTypeArguments;

    List<TypeArgumentInfo>[] superInterfacesTypeArguments;

    ClassFile() {
        super();
    }

    void setSuperName(String superName) {
        this.superName = superName;
        if (superName != null) {
            this.superName = superName.intern();
        }
    }

    public final String getTypeName() {
        return fullName;
    }

    public final String getSuperClassName() {
        return superName;
    }

    public final List<TypeArgumentInfo> getSuperClassTypeArguments() {
        return superClassTypeArguments;
    }

    public final String[] getInterfaceNames() {
        return interfaceNames;
    }

    void setInterfaceNames(String[] interfaceNames) {
        this.interfaceNames = interfaceNames;
        if (interfaceNames != null) {
            for (int i = 0; i < interfaceNames.length; i++) {
                interfaceNames[i] = interfaceNames[i].intern();
            }
        }
    }

    public final List<TypeArgumentInfo> getSuperInterfaceTypeArguments(int ifidx) {
        return superInterfacesTypeArguments == null ? null : superInterfacesTypeArguments[ifidx];
    }

    public final List<FieldInfo> getFieldInfos() {
        return fields;
    }

    public final List<MethodInfo> getMethodInfos() {
        return methods;
    }

    public final List<ConstructorInfo> getConstructorInfos() {
        return constructors;
    }

    public final String[] getInnerClassNames() {
        return innerClasses;
    }

    void setInnerClassNames(String[] innerClassNames) {
        this.innerClasses = innerClassNames;
        if (innerClasses != null) {
            for (int i = 0; i < innerClassNames.length; i++) {
                innerClassNames[i] = innerClassNames[i].intern();
            }
        }
    }

    public final String getFullName() {
        return fullName;
    }

    void setFullName(String fullName) {
        this.fullName = fullName.intern();
    }

    public final String getPhysicalName() {
        return physicalName;
    }

    void setPhysicalName(String phkName) {
        this.physicalName = phkName;
    }

    public final ClassTypeContainer getContainer() {
        return service.getClassTypeContainer(this);
    }

    public ClassType getContainingClassType() {
        ClassTypeContainer ctc = service.getClassTypeContainer(this);
        return (ctc instanceof ClassType) ? (ClassType) ctc : null;
    }

    public final Package getPackage() {
        return service.getPackage(this);
    }

    public final boolean isInterface() {
        return (accessFlags & AccessFlags.INTERFACE) != 0;
    }

    public boolean isOrdinaryInterface() {
        return (accessFlags & AccessFlags.INTERFACE) != 0
                && (accessFlags & AccessFlags.ANNOTATION) == 0;
    }

    public boolean isAnnotationType() {
        return (accessFlags & AccessFlags.ANNOTATION) != 0;
    }

    public boolean isEnumType() {
        return (accessFlags & AccessFlags.ENUM) != 0;
    }

    public boolean isOrdinaryClass() {
        return (accessFlags & AccessFlags.INTERFACE) == 0 && (accessFlags & AccessFlags.ENUM) == 0;
    }

    public final List<ClassType> getSupertypes() {
        return service.getSupertypes(this);
    }

    public final List<ClassType> getAllSupertypes() {
        return service.getAllSupertypes(this);
    }

    @SuppressWarnings("unchecked")
    public final List<FieldInfo> getFields() {
        return (List<FieldInfo>) service.getFields(this);
    }

    void setFields(List<FieldInfo> fields) {
        this.fields = fields;
    }

    public final List<Field> getAllFields() {
        return service.getAllFields(this);
    }

    public final List<Method> getMethods() {
        return service.getMethods(this);
    }

    void setMethods(List<MethodInfo> methods) {
        this.methods = methods;
    }

    public final List<Method> getAllMethods() {
        return service.getAllMethods(this);
    }

    public final List<? extends Constructor> getConstructors() {
        return service.getConstructors(this);
    }

    void setConstructors(List<ConstructorInfo> constructors) {
        this.constructors = constructors;
    }

    @SuppressWarnings("unchecked")
    public final List<ClassFile> getTypes() {
        return (List<ClassFile>) service.getTypes(this);
    }

    public final List<ClassType> getAllTypes() {
        return service.getAllTypes(this);
    }

    /**
     * @return a list of annotations
     */
    public List<AnnotationUseInfo> getAnnotations() {
        return annotations;
    }

    void setAnnotations(List<AnnotationUseInfo> annotations) {
        this.annotations = annotations;
    }

    public List<TypeParameterInfo> getTypeParameters() {
        return typeParams;
    }

    public void setTypeParameters(List<TypeParameterInfo> typeParams) {
        this.typeParams = typeParams;
    }

    public String getLocation() {
        return location;
    }

    void setLocation(String location) {
        this.location = location;
    }

    @Override
    public String toString() {
        return "ClassFile " + getFullName();
    }

}
