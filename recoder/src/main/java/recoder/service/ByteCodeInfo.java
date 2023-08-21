/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import recoder.abstraction.*;
import recoder.bytecode.*;

/**
 * Implements queries for program model elements with bytecode representations.
 */
public interface ByteCodeInfo extends ProgramModelInfo {

    /**
     * Registers a new class file for the service.
     *
     * @param cf the new class file.
     */
    void register(ClassFile cf);

    /**
     * Returns the bytecode counterpart of the given classtype. Returns <CODE>
     * null</CODE>, if the given type is not a class file.
     *
     * @param ct a class type.
     * @param the corresponding class file, or <CODE>null</CODE>, if the given type has no bytecode
     *        representation.
     */
    ClassFile getClassFile(ClassType ct);

    /**
     * Returns the bytecode counterpart of the given method. Returns <CODE>null
     * </CODE>, if the given method is not a method info.
     *
     * @param m a method.
     * @param the corresponding bytecode element, or <CODE>null</CODE>, if the given method has no
     *        bytecode representation.
     */
    MethodInfo getMethodInfo(Method m);

    /**
     * Returns the bytecode counterpart of the given constructor. Returns <CODE>
     * null</CODE>, if the given constructor is not a constructor info.
     *
     * @param c a constructor.
     * @param the corresponding bytecode element, or <CODE>null</CODE>, if the given constructor has
     *        no bytecode representation.
     */
    ConstructorInfo getConstructorInfo(Constructor c);

    /**
     * Returns the bytecode counterpart of the given field. Returns <CODE>null
     * </CODE>, if the given field is not a field info.
     *
     * @param f a field.
     * @param the corresponding field info, or <CODE>null</CODE>, if the given field has no bytecode
     *        representation.
     */
    FieldInfo getFieldInfo(Field f);


    /**
     * Returns the (annotation) type of the given annotation use.
     *
     * @param au an annotation use
     * @return the type of the referenced annotation type
     */
    Type getAnnotationType(AnnotationUseInfo au);

}
