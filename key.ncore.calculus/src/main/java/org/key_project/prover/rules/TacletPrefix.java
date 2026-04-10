/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

public interface TacletPrefix {
    boolean context();

    /// returns a new TacletPrefix with the context flag set to the given boolean value
    ///
    /// @param setTo the boolean to which the TacletPrefix is set to
    /// @return a newly created TacletPrefix
    TacletPrefix setContext(boolean setTo);
}
