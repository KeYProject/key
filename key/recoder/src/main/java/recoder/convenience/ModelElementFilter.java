/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.convenience;

import recoder.ModelElement;

/**
 * Filter predicate for model elements.
 *
 * @author AL
 */
public interface ModelElementFilter {
    /**
     * Accepts or denies a given model element.
     *
     * @param e the model element to value.
     * @return true iff the given element is accepted by the filter.
     */
    boolean accept(ModelElement e);
}
