/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

/**
 * A program model element representing constructors. Constructors are modelled as subtypes of
 * methods and will return <CODE>null</CODE> as return type.
 *
 * @author AL
 * @author RN
 */
public interface Constructor extends Method {
    // no additional members
}
