/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.ProofAggregate;


/**
 * Represents something that produces an input proof obligation for the prover. A .key file or a
 * proof obligation generated from a CASE tool may be instances.
 */
public interface ProofOblInput {

    /**
     * Returns the name of the proof obligation input.
     */
    String name();

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

    /**
     * Returns the {@link KeYJavaType} in which the proven element is contained in.
     *
     * @return The {@link KeYJavaType} in which the proven element is contained in or {@code null}
     *         if not available.
     */
    KeYJavaType getContainerType();
}
