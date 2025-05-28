/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof;

import org.key_project.prover.rules.instantiation.caches.AssumesFormulaInstantiationCache;

/// Provides access to caches used during proof search
public interface SessionCaches {
    /// returns the cache relevant for matching assumes formulas
    ///
    /// @return the cache relevant for matching assumes formulas
    AssumesFormulaInstantiationCache getAssumesFormulaInstantiationCache();
}
