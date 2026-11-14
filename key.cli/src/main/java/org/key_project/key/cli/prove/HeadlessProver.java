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
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ResultStatus;
import org.key_project.prover.engine.ProofSearchInformation;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Headless driver that loads a KeY problem and proves the selected contracts, producing one
 * {@link ContractResult} per contract.
 * <p>
 * The selection precedence is: explicit {@code --choose-contract} selectors, then the contract
 * selected by a {@code \chooseContract}/{@code \proofObligation} directive in the load file,
 * then all contracts of the stable index (§4.2 of the headless interface spec).
 * <p>
 * Per-contract failures are reported as {@link ResultStatus#ERROR} results (never thrown);
 * failures to load the problem file surface as {@link ProblemLoaderException} and unknown
 * selectors as {@link UnknownContractException}.
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
     * Loads the given problem file and proves the contracts selected by the load file's
     * {@code \chooseContract}/{@code \proofObligation} directive, or all of its contracts if the
     * load file selects none.
     *
     * @param problem the KeY problem file ({@code .key}) to load
     * @return one {@link ContractResult} per selected contract, in selection order
     * @throws ProblemLoaderException if the problem file cannot be loaded
     * @throws UnknownContractException declared for symmetry with {@link #prove(Path, List)}
     *         although no selector can be unknown without selectors
     */
    public List<ContractResult> proveAll(Path problem) throws ProblemLoaderException,
            UnknownContractException {
        return prove(problem, List.of());
    }

    /**
     * Loads the given problem file and proves the contracts selected by the given
     * {@code --choose-contract} selectors. Without selectors, the load file's
     * {@code \chooseContract}/{@code \proofObligation} directive selects the contract, and
     * without a directive all contracts of the stable index are selected.
     *
     * @param problem the KeY problem file ({@code .key}) to load
     * @param selectors the {@code --choose-contract} selector values in command-line order
     * @return one {@link ContractResult} per selected contract, in selection order
     * @throws ProblemLoaderException if the problem file cannot be loaded
     * @throws UnknownContractException if a selector matches no contract of the problem
     */
    public List<ContractResult> prove(Path problem, List<String> selectors)
            throws ProblemLoaderException, UnknownContractException {
        KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(problem);
        try {
            ContractIndex index = ContractIndex.fromEnvironment(environment);
            List<Contract> selected = select(environment, index, selectors);
            List<ContractResult> results = new ArrayList<>(selected.size());
            for (Contract contract : selected) {
                results.add(prove(environment, contract));
            }
            return results;
        } finally {
            environment.dispose();
        }
    }

    private static List<Contract> select(KeYEnvironment<?> environment, ContractIndex index,
            List<String> selectors) throws UnknownContractException {
        if (!selectors.isEmpty()) {
            return ContractSelector.resolve(index, selectors);
        }
        Contract loadFileContract = loadFileContract(environment);
        return loadFileContract != null ? List.of(loadFileContract) : index.contracts();
    }

    /**
     * Returns the contract selected by a {@code \chooseContract}/{@code \proofObligation}
     * directive of the loaded problem, or {@code null} if the load file does not select a
     * contract (e.g. it defines a plain {@code \problem}).
     */
    private static @Nullable Contract loadFileContract(KeYEnvironment<?> environment) {
        Proof loaded = environment.getLoadedProof();
        if (loaded == null) {
            return null;
        }
        ProofOblInput po =
            environment.getServices().getSpecificationRepository().getProofOblInput(loaded);
        return po instanceof ContractPO contractPO ? contractPO.getContract() : null;
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
