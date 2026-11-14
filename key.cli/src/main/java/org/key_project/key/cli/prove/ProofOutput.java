/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.nio.file.Path;

import org.jspecify.annotations.Nullable;

/**
 * The requested proof-file output of a prove run (§3 of the headless interface spec).
 *
 * @param proof the explicit single-contract output path ({@code --proof}), or {@code null}
 * @param proofDir the multi-contract output directory ({@code --proof-dir}), or {@code null};
 *        files are named {@code <position>.proof}, where the position is the 0-based index of
 *        the contract within the selection (not its global index)
 * @param savePartial whether an unclosed proof may be written as well ({@code --save-partial})
 */
public record ProofOutput(@Nullable Path proof, @Nullable Path proofDir, boolean savePartial) {

    /// No proof file requested: nothing is written, even for closed proofs.
    public static ProofOutput none() {
        return new ProofOutput(null, null, false);
    }

    /**
     * Returns the output file for the contract at the given selection position, or {@code null}
     * if no output location was requested.
     *
     * @param position the 0-based position of the contract within the selection
     * @return the requested output file, or {@code null}
     */
    public @Nullable Path targetFor(int position) {
        if (proof != null) {
            return proof;
        }
        if (proofDir != null) {
            return proofDir.resolve(position + ".proof");
        }
        return null;
    }
}
