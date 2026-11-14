/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ResultStatus;
import org.key_project.prover.engine.ProofSearchInformation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Headless driver that loads a KeY problem and proves all its contracts, producing one
 * {@link ContractResult} per contract.
 * <p>
 * Per-contract failures are reported as {@link ResultStatus#ERROR} results (never thrown); only
 * failures to load the problem file surface as {@link ProblemLoaderException}.
 */
public final class HeadlessProver {

    private static final Logger LOGGER = LoggerFactory.getLogger(HeadlessProver.class);

    private final long timeoutMs;

    /**
     * Creates a prover without a timeout.
     */
    public HeadlessProver() {
        this(0);
    }

    /**
     * Creates a prover with an optional per-contract timeout.
     *
     * @param timeoutMs the proof-search timeout in milliseconds, or {@code 0} for no timeout
     */
    public HeadlessProver(long timeoutMs) {
        this.timeoutMs = Math.max(0, timeoutMs);
    }

    /**
     * Loads the given problem file and proves all of its contracts.
     *
     * @param problem the KeY problem file ({@code .key}) to load
     * @return one {@link ContractResult} per contract, in the stable index order
     * @throws ProblemLoaderException if the problem file cannot be loaded
     */
    public List<ContractResult> proveAll(Path problem) throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(problem);
        try {
            ContractIndex index = ContractIndex.fromEnvironment(environment);
            List<ContractResult> results = new ArrayList<>(index.size());
            for (Contract contract : index.contracts()) {
                results.add(prove(environment, contract));
            }
            return results;
        } finally {
            environment.dispose();
        }
    }

    private ContractResult prove(KeYEnvironment<?> environment, Contract contract) {
        long start = System.nanoTime();
        Proof proof = null;
        try {
            ContractPO obligation = contract.createProofObl(environment.getInitConfig());
            proof = environment.createProof(obligation);

            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            if (timeoutMs > 0) {
                starter.setTimeout(timeoutMs);
            }
            ProofSearchInformation<Proof, Goal> info = starter.start();

            boolean closed = proof.closed() || proof.openGoals().isEmpty();
            int openGoals = proof.openGoals().size();
            LOGGER.debug("Contract '{}' finished after {} ms with {} open goals",
                contract.getName(),
                info.getTime(), openGoals);
            return new ContractResult(contract.getName(),
                closed ? ResultStatus.CLOSED : ResultStatus.OPEN, openGoals,
                elapsedMs(start), null, 0, 0, null);
        } catch (Exception e) {
            LOGGER.debug("Proving contract '{}' failed", contract.getName(), e);
            return new ContractResult(contract.getName(), ResultStatus.ERROR, 0, elapsedMs(start),
                null, 0, 0, errorMessage(e));
        } finally {
            if (proof != null && !proof.isDisposed()) {
                proof.dispose();
            }
        }
    }

    private static long elapsedMs(long startNanos) {
        return TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - startNanos);
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
