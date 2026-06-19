/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof;

/// provides access to services related to proof search
public interface ProofServices {
    /// provides access to the caching infrastructure of a proof session
    ///
    /// @return the caches used during proof search
    SessionCaches getCaches();
}
