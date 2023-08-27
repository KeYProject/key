/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.List;

import recoder.Service;
import recoder.abstraction.*;
import recoder.abstraction.Package;

/**
 * Manages the global name mapping.
 */
public interface NameInfo extends Service {

    /**
     * Returns a package represented by the given fully qualified name. If the package has not been
     * encountered before, a new package is created and returned.
     *
     * @param name a qualified name.
     * @return the according package, constructed on demand.
     */
    Package createPackage(String name);

    /**
     * Returns the package represented by the given fully qualified name, if it already exists.
     *
     * @param name a qualified name.
     * @return the according package, or <CODE>null</CODE>.
     */
    Package getPackage(String name);

    /**
     * Returns the list of globally known packages.
     *
     * @return the list of packages.
     */
    List<Package> getPackages();

    /**
     * Returns the type represented by the given fully qualified name. If the type is currently not
     * available, the method returns <tt>null</tt>. A type may be unavailable either if it currently
     * has not been analyzed or is undefined. The specific behavior depends on the compiler
     * configuration.
     *
     * @param name a fully qualified type name.
     * @return the according type, or <tt>null</tt>.
     */
    Type getType(String name);

    /**
     * Returns the list of globally known types.
     *
     * @return the list of types.
     */
    List<Type> getTypes();

    /**
     * Returns the list of known class types of the given package.
     *
     * @param pkg a package.
     * @return the list of class types in the package.
     */
    List<ClassType> getTypes(Package pkg);

    /**
     * Returns the class type represented by the given fully qualified name. If the type is
     * currently not available or does not represent a class type, the method returns <tt>null</tt>.
     *
     * @param name a fully qualified type name.
     * @return the according class type, or <tt>null</tt>.
     */
    ClassType getClassType(String name);

    /**
     * Returns the array type for the given base type, if it already exists.
     *
     * @param basetype the base type to find an array type for.
     * @return the array type for the given base type, or <CODE>null</CODE>.
     */
    ArrayType getArrayType(Type basetype);

    /**
     * Returns the array type for the given base type. This method will create one if needed. Same
     * as <code>createArrayType(basetype, 1)</code>
     *
     * @param basetype the base type to find an array type for.
     * @return the array type for the given base type.
     */
    ArrayType createArrayType(Type basetype);

    /**
     * Returns the array type for the given base type with the given dimensions. This method will
     * create one if needed.
     *
     * @param basetype the base type to find an array type for.
     * @param dimensions
     * @return the array type for the given base type.
     */
    ArrayType createArrayType(Type basetype, int dimensions);

    /**
     * Returns the list of globally known class types.
     *
     * @return the list of class types.
     */
    List<ClassType> getClassTypes();

    /**
     * Returns the predefined Null type. The Null type is widening to each class or array type.
     *
     * @return the Null type.
     */
    ClassType getNullType();

    /**
     * Returns the predefined boolean type.
     *
     * @return the primitive boolean type.
     */
    PrimitiveType getBooleanType();

    /**
     * Returns the predefined byte type.
     *
     * @return the primitive byte type.
     */
    PrimitiveType getByteType();

    /**
     * Returns the predefined short type.
     *
     * @return the primitive short type.
     */
    PrimitiveType getShortType();

    /**
     * Returns the predefined int type.
     *
     * @return the primitive int type.
     */
    PrimitiveType getIntType();

    /**
     * Returns the predefined long type.
     *
     * @return the primitive long type.
     */
    PrimitiveType getLongType();

    /**
     * Returns the predefined float type.
     *
     * @return the primitive float type.
     */
    PrimitiveType getFloatType();

    /**
     * Returns the predefined double type.
     *
     * @return the primitive double type.
     */
    PrimitiveType getDoubleType();

    /**
     * Returns the predefined char type.
     *
     * @return the primitive char type.
     */
    PrimitiveType getCharType();

    /**
     * Returns the predefined Object type.
     *
     * @return the Object type.
     */
    ClassType getJavaLangObject();

    /**
     * Returns the predefined String type.
     *
     * @return the String type.
     */
    ClassType getJavaLangString();

    /**
     * Returns the predefined Boolean type.
     *
     * @return the Boolean type.
     * @since 0.8
     */
    ClassType getJavaLangBoolean();

    /**
     * Returns the predefined Byte type.
     *
     * @return the Byte type.
     * @since 0.8
     */
    ClassType getJavaLangByte();

    /**
     * Returns the predefined Character type.
     *
     * @return the Character type.
     * @since 0.8
     */
    ClassType getJavaLangCharacter();

    /**
     * Returns the predefined Short type.
     *
     * @return the Short type.
     * @since 0.8
     */
    ClassType getJavaLangShort();

    /**
     * Returns the predefined Integer type.
     *
     * @return the Integer type.
     * @since 0.8
     */
    ClassType getJavaLangInteger();

    /**
     * Returns the predefined Long type.
     *
     * @return the Long type.
     * @since 0.8
     */
    ClassType getJavaLangLong();

    /**
     * Returns the predefined Float type.
     *
     * @return the Float type.
     * @since 0.8
     */
    ClassType getJavaLangFloat();

    /**
     * Returns the predefined Double type.
     *
     * @return the Double type.
     * @since 0.8
     */
    ClassType getJavaLangDouble();

    /**
     * Returns the predefined Class type. The Class type appears as the type of ".class" references.
     *
     * @return the Class type.
     */
    ClassType getJavaLangClass();

    /**
     * Returns the predefined Cloneable type. The Cloneable type is a valid supertype of arrays.
     *
     * @return the Cloneable type.
     */
    ClassType getJavaLangCloneable();

    /**
     * Returns the predefined Serializable type. The Serializable type is a valid supertype of
     * arrays.
     *
     * @return the Serializable type.
     */
    ClassType getJavaIoSerializable();

    /**
     * Returns the predefined interface java.lang.annotation.Annotation.
     *
     * @return the Annotation type
     */
    ClassType getJavaLangAnnotationAnnotation();


    /**
     * Returns the predefined class java.lang.Enum.
     *
     * @return the Annotation type
     */
    ClassType getJavaLangEnum();

    /**
     * Returns a field belonging to the given fully qualified name.
     *
     * @param a fully qualified field name, e.g. "System.out".
     * @return the field with that name, or <tt>null</tt> if no such field is known.
     */
    Field getField(String name);

    /**
     * Returns the list of globally known fields.
     *
     * @return the list of fields.
     */
    List<Field> getFields();

    /**
     * Registers a class type.
     *
     * @param ct the class type to be recognized by this service.
     */
    void register(ClassType ct);

    /**
     * Registers a field.
     *
     * @param f the field to be recognized by this service.
     */
    void register(Field f);

    /**
     * Unregisters a class type.
     *
     * @param fullname the (former) class type name.
     */
    void unregisterClassType(String fullname);

    /**
     * Unregisters a field.
     *
     * @param fullname the (former) field name.
     */
    void unregisterField(String fullname);

    /**
     * Returns the placeholder for an unknown entity that might be a package, class type, or field.
     * Unknown elements can model incomplete programs. Queries for properties of unknown elements
     * will return only minimum information, even though it often is possible to infer certain
     * information about single unknown elements. As the alias problem is not solvable, there is
     * only one representative for all unknown elements of a certain type.
     */
    ProgramModelElement getUnknownElement();

    /**
     * Returns the placeholder for an unknown type. Unknown elements can model incomplete programs.
     * Queries for properties of unknown elements will return only minimum information, even though
     * it often is possible to infer certain information about single unknown elements. As the alias
     * problem is not solvable, there is only one representative for all unknown elements of a
     * certain type.
     */
    Type getUnknownType();

    /**
     * Returns the placeholder for an unknown class type. Unknown elements can model incomplete
     * programs. Queries for properties of unknown elements will return only minimum information,
     * even though it often is possible to infer certain information about single unknown elements.
     * As the alias problem is not solvable, there is only one representative for all unknown
     * elements of a certain type.
     */
    ClassType getUnknownClassType();

    /**
     * Returns the placeholder for an unknown package. Unknown elements can model incomplete
     * programs. Queries for properties of unknown elements will return only minimum information,
     * even though it often is possible to infer certain information about single unknown elements.
     * As the alias problem is not solvable, there is only one representative for all unknown
     * elements of a certain type.
     */
    Package getUnknownPackage();

    /**
     * Returns the placeholder for an unknown method. Unknown elements can model incomplete
     * programs. Queries for properties of unknown elements will return only minimum information,
     * even though it often is possible to infer certain information about single unknown elements.
     * As the alias problem is not solvable, there is only one representative for all unknown
     * elements of a certain type.
     */
    Method getUnknownMethod();

    /**
     * Returns the placeholder for an unknown constructor. Unknown elements can model incomplete
     * programs. Queries for properties of unknown elements will return only minimum information,
     * even though it often is possible to infer certain information about single unknown elements.
     * As the alias problem is not solvable, there is only one representative for all unknown
     * elements of a certain type.
     */
    Constructor getUnknownConstructor();

    /**
     * Returns the placeholder for an unknown variable. Unknown elements can model incomplete
     * programs. Queries for properties of unknown elements will return only minimum information,
     * even though it often is possible to infer certain information about single unknown elements.
     * As the alias problem is not solvable, there is only one representative for all unknown
     * elements of a certain type.
     */
    Variable getUnknownVariable();

    /**
     * Returns the placeholder for an unknown field. Unknown elements can model incomplete programs.
     * Queries for properties of unknown elements will return only minimum information, even though
     * it often is possible to infer certain information about single unknown elements. As the alias
     * problem is not solvable, there is only one representative for all unknown elements of a
     * certain type.
     */
    Field getUnknownField();

    /**
     * Returns the placeholder for an unknown annotation property. Unknown elements can model
     * incomplete programs. Queries for properties of unknown elements will return only minimum
     * information, even though it often is possible to infer certain information about single
     * unknown elements. As the alias problem is not solvable, there is only one representative for
     * all unknown elements of a certain type.
     */
    AnnotationProperty getUnknownAnnotationProperty();
}
