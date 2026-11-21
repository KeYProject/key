/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import de.uka.ilkd.key.proof.init.ProofInputException;

import org.key_project.key.cli.CliError;
import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ResultStatus;

/**
 * Signals that the proof obligation of a contract could not be created: the load file parsed,
 * but KeY cannot build a proof for the selected contract (a {@link ProofInputException} from
 * the proof initializer). Per §1 of the headless interface spec this is an <em>input</em> error
 * (exit 3), and both the {@code prove} and {@code script} subcommands report it identically:
 * first the {@code "status":"error"} result record of {@link #record()} on stdout, then the
 * {@link CliError} input error of {@link #cliError()} (a {@code KEY_ERROR} line on stderr).
 */
public final class ObligationCreationException extends RuntimeException {

    private final transient String contract;

    private final transient String message;

    /**
     * Creates the exception for the failed obligation.
     *
     * @param contract the canonical name of the contract whose obligation could not be created
     * @param cause the {@link ProofInputException} thrown while creating the proof
     */
    public ObligationCreationException(String contract, ProofInputException cause) {
        super(messageFor(contract, cause), cause);
        this.contract = contract;
        this.message = messageFor(contract, cause);
    }

    private static String messageFor(String contract, ProofInputException cause) {
        return "cannot create the proof obligation for '" + contract + "': " + reason(cause);
    }

    /**
     * Returns the canonical name of the contract whose obligation could not be created.
     *
     * @return the contract name, verbatim
     */
    public String contract() {
        return contract;
    }

    /**
     * Returns the {@code "status":"error"} result record reported for the failed contract,
     * whose {@code errorMessage} carries the same message as the {@code KEY_ERROR} line.
     *
     * @return the error record for the failed contract
     */
    public ContractResult record() {
        return new ContractResult(contract, ResultStatus.ERROR, 0, 0, null, 0, 0,
            CliError.oneLine(message));
    }

    /**
     * Returns the classified CLI error for this failure: an input error (exit 3) carrying the
     * same message as the {@code KEY_ERROR} line.
     *
     * @return the input error to throw
     */
    public CliError cliError() {
        return CliError.input(message, this);
    }

    private static String reason(ProofInputException cause) {
        String message = cause.getMessage();
        return CliError.oneLine(message != null ? message : cause.getClass().getSimpleName());
    }
}
