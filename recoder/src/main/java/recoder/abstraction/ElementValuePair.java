/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.abstraction;

/**
 * @author Tobias Gutzmann
 */
public interface ElementValuePair {
    /**
     * Returns the value. Can be either of
     * <ul>
     * <li>any boxed primitive type
     * <li>java.lang.String
     * <li>any subtype of java.lang.Class
     * <li>
     * <li>a one-dimensional array of any of the above.
     * </ul>
     *
     * @return
     */
    Object getValue();

    String getElementName();

    // String getFullNameOfContainingAnnotation();
}
