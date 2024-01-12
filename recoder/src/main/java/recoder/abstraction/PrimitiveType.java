/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import recoder.service.ProgramModelInfo;

/**
 * A program model element representing primitive types.
 *
 * @author AL
 * @author RN
 */
public class PrimitiveType implements Type {

    private final String name;

    private ProgramModelInfo pmi;

    public PrimitiveType(String name, ProgramModelInfo pmi) {
        this.name = name.intern();
        this.pmi = pmi;
    }

    /**
     * Returns the name of this type.
     *
     * @return the name of this type.
     */
    public String getName() {
        return name;
    }

    /**
     * Returns the name of type.
     *
     * @return the full name of this program model element.
     */
    public String getFullName() {
        return name;
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

    public PrimitiveType deepClone() {
        throw new UnsupportedOperationException("Cannot deep-clone primitive types");
    }

}
