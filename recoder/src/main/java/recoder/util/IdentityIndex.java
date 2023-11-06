/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * @author AL
 */
public class IdentityIndex extends AbstractIndex {

    public IdentityIndex() {
        super();
    }

    public IdentityIndex(int initialCapacity) {
        super(initialCapacity);
    }

    public final int hashCode(Object o) {
        return System.identityHashCode(o);
    }

    public final boolean equals(Object p, Object q) {
        return p == q;
    }
}
