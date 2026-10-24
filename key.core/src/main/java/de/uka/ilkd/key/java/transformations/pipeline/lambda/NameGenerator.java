/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import java.util.HashSet;
import java.util.Set;

/**
 * Generates names that are unique within one instance of this generator.
 * <p>
 * A fresh instance is used per {@link com.github.javaparser.ast.CompilationUnit}, which
 * guarantees that all names generated during desugaring of one compilation unit are
 * pairwise distinct.
 *
 * @author weigl, csicar
 */
public class NameGenerator {
    private final Set<String> used = new HashSet<>();

    /**
     * Returns a fresh name of the form {@code prefix__N} for a strictly increasing
     * counter N (starting at 1), unique within this generator.
     */
    public String fresh(String prefix) {
        String candidate;
        for (int i = 1;; i++) {
            candidate = prefix + "__" + i;
            if (used.add(candidate)) {
                return candidate;
            }
        }
    }

    /**
     * Returns {@code base} if it is not yet used by this generator, otherwise the
     * first {@code base_N} (N &ge; 2) not yet used.
     */
    public String freshName(String base) {
        if (used.add(base)) {
            return base;
        }
        String candidate;
        for (int i = 2;; i++) {
            candidate = base + "_" + i;
            if (used.add(candidate)) {
                return candidate;
            }
        }
    }
}
