/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

/**
 * Simple counter to produce a sequence of numbers.
 *
 * @author Arne Keller
 */
public class IndexFactory {
    /**
     * Next index to return.
     */
    private int idx = 0;

    /**
     * Returns the smallest int not yet returned by this method.
     * That is, the first call will return 0, the next call 1, and so on...
     *
     * @return an index
     */
    public int nextIndex() {
        int i = idx;
        idx++;
        return i;
    }
}
