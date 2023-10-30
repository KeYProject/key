/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * @author AL
 */
public class NaturalIndex extends AbstractIndex {

    public NaturalIndex() {
        super();
    }

    public NaturalIndex(int initialCapacity) {
        super(initialCapacity);
    }

    public final int hashCode(Object o) {
        return o.hashCode();
    }

    public final boolean equals(Object p, Object q) {
        return p.equals(q);
    }
}
