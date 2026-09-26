/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

/**
 * Spec math modes
 */
public enum SpecMathMode {
    /** Bigint arithmetic */
    BIGINT,
    /** Java semantics */
    JAVA,
    /** Bigint arithmetic with checked overflows */
    SAFE;

    /**
     * Default spec math mode
     */
    public static SpecMathMode defaultMode() {
        return BIGINT;
    }
}
