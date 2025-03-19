/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import recoder.abstraction.AnnotationProperty;

/**
 * @author gutzmann
 */
public class AnnotationPropertyInfo extends MethodInfo implements AnnotationProperty {

    private final Object defaultValue;

    /**
     * @param accessFlags
     * @param returntype
     * @param name
     * @param cf
     * @param defaultValue
     */
    public AnnotationPropertyInfo(int accessFlags, String returntype, String name, ClassFile cf,
            Object defaultValue) {
        super(accessFlags, returntype, name, new String[0], new String[0], cf);
        this.defaultValue = defaultValue;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.abstraction.AnnotationProperty#getDefaultValue()
     */
    public Object getDefaultValue() {
        return defaultValue;
    }

}
