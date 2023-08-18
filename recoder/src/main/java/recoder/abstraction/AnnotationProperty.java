/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;


/**
 * @author gutzmann
 *         <p>
 *         a program model element representing annotation properties.
 */
public interface AnnotationProperty extends Method {
    /**
     * Returns the default value for the annotation member represented by this Method instance.
     * Returns null if no default is associated with the member, or if the method instance does not
     * represent a declared member of an annotation type.
     *
     * @return the default value for the annotation member represented by this Method instance.
     */
    Object getDefaultValue();
}
