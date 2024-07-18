/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;

import org.key_project.logic.Named;
import org.key_project.rusty.proof.ProofAggregate;

/**
 * Represents something that produces an input proof obligation for the prover. A .key file or a
 * proof obligation generated from a CASE tool may be instances.
 */
public interface ProofOblInput extends Named {

    void readProblem() throws ProofInputException;

    /**
     * Returns the proof obligation term as result of the proof obligation input. If there is still
     * no input available because nothing has been read yet null is returned.
     */
    ProofAggregate getPO() throws ProofInputException;

    /**
     * If true, then this PO implies the passed one.
     */
    boolean implies(ProofOblInput po);
}
