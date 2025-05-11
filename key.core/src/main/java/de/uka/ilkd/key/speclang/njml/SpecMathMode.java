/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import org.jspecify.annotations.NonNull;

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
    public static @NonNull SpecMathMode defaultMode() {
        return BIGINT;
    }
}
