/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import recoder.bytecode.MethodInfo;
import recoder.service.ProgramModelInfo;

/**
 * A program model element representing array types.
 *
 * @author AL
 * @author RN
 */
public class ArrayType implements Type {

    private final Type basetype;
    ProgramModelInfo pmi;
    private String shortName;
    private String fullName;

    /**
     * Creates a new array type for the given base type, organized by the given program model info.
     *
     * @param basetype the base type of the array.
     * @param pmi the program model info responsible for this type.
     */
    public ArrayType(Type basetype, ProgramModelInfo pmi) {
        this.basetype = basetype;
        this.pmi = pmi;
        makeNames();
    }

    /**
     * this is for internal recoder use only. NameInfo needs to rebuild the array type names when
     * the base type has been renamed. However, calling this does not do any harm.
     */
    public void makeNames() {
        shortName = basetype.getName() + "[]";
        fullName = basetype.getFullName() + "[]";
    }

    /**
     * Returns the base type of this array type.
     *
     * @return the base type.
     */
    public Type getBaseType() {
        return basetype;
    }

    /**
     * Returns the name of this array type.
     *
     * @return the name of this type.
     */
    public String getName() {
        return shortName;
    }

    /**
     * Returns the maximal expanded name including all applicable qualifiers.
     *
     * @return the full name of this program model element.
     */
    public String getFullName() {
        return fullName;
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
     * @param service the program model info for this element.
     */
    public void setProgramModelInfo(ProgramModelInfo service) {
        this.pmi = service;
    }

    public void validate() {
        // not checked yet
    }

    public MethodInfo deepClone() {
        throw new UnsupportedOperationException("Cannot deep-clone implicit information");
    }

}
