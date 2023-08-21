/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
