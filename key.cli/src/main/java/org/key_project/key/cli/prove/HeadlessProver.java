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
import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.ResultStatus;
import org.key_project.key.cli.settings.HeadlessRunnerSettings;
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
 * <p>
 * A positive timeout bounds each contract's proof search ({@link ProofStarter#setTimeout(long)});
 * a search abandoned by the timeout is reported as {@link ResultStatus#TIMED_OUT} (exit code
 * {@code 2}), while a search that exhausts the strategy without a timeout in effect stays
 * {@link ResultStatus#OPEN} (exit code {@code 1}).
 * <p>
 * The {@code smtCalls}/{@code smtProved} fields of the result records are computed from the
 * finished proof by {@link SmtCounters} ({@code 0}/{@code 0} when SMT is not used, the default).
 */
public final class HeadlessProver {

    private static final Logger LOGGER = LoggerFactory.getLogger(HeadlessProver.class);

    /**
     * Value passed to {@link ProofStarter#setTimeout(long)} for {@code --timeout 0}: a non-negative
     * value enables the stop condition's time limit, while {@code -1} disables it.
     */
    private static final long NO_TIMEOUT = -1L;

    private final long timeoutMs;

    private final @Nullable HeadlessRunnerSettings runnerSettings;

    /**
     * Creates a prover without a timeout.
     */
    public HeadlessProver() {
        this(0, null);
    }

    /**
     * Creates a prover with an optional per-contract timeout.
     *
     * @param timeoutMs the proof-search timeout in milliseconds, or {@code 0} for no timeout
     */
    public HeadlessProver(long timeoutMs) {
        this(timeoutMs, null);
    }

    /**
     * Creates a prover with an optional per-contract timeout and per-run strategy settings.
     *
     * @param timeoutMs the proof-search timeout in milliseconds, or {@code 0} for no timeout
     * @param runnerSettings the §5.1 strategy settings to apply for the whole run, or {@code null}
     *        if none were requested
     */
    public HeadlessProver(long timeoutMs, @Nullable HeadlessRunnerSettings runnerSettings) {
        this.timeoutMs = Math.max(0, timeoutMs);
        this.runnerSettings = runnerSettings;
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
        HeadlessRunnerSettings settings = runnerSettings;
        if (settings != null) {
            settings.apply();
        }
        try {
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
        } finally {
            if (settings != null) {
                settings.close();
            }
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
            starter.setTimeout(timeoutMs > 0 ? timeoutMs : NO_TIMEOUT);
            ProofSearchInformation<Proof, Goal> info = starter.start();

            long elapsedMs = info.getTime();
            int openGoals = proof.openGoals().size();
            boolean closed = proof.closed() || openGoals == 0;
            ResultStatus status = classifyStatus(closed, timeoutMs, elapsedMs);
            SmtCounters.Counts smt = SmtCounters.of(proof);
            LOGGER.debug("Contract '{}' finished after {} ms with {} open goals (status {})",
                contract.getName(),
                elapsedMs, openGoals, status);
            return new ContractResult(contract.getName(), status, openGoals, elapsedMs, null,
                smt.smtCalls(), smt.smtProved(), null);
        } catch (Exception e) {
            LOGGER.debug("Proving contract '{}' failed", contract.getName(), e);
            return errorResult(contract.getName(), elapsedMs(start), e);
        } finally {
            if (proof != null && !proof.isDisposed()) {
                proof.dispose();
            }
        }
    }

    /**
     * Creates the {@link ResultStatus#ERROR} result for a contract whose proof attempt failed:
     * the record carries a non-{@code null} {@code errorMessage} and maps to the internal-error
     * exit code {@code 4} via {@link ExitCode#worstOf}.
     *
     * @param contract the canonical name of the contract that failed
     * @param elapsedMs wall-clock milliseconds spent on the failed attempt
     * @param failure the exception thrown during the proof attempt
     * @return the error result for the contract
     */
    static ContractResult errorResult(String contract, long elapsedMs, Exception failure) {
        return new ContractResult(contract, ResultStatus.ERROR, 0, elapsedMs, null, 0, 0,
            errorMessage(failure));
    }

    /**
     * Classifies the final status of a contract after proof search (§1 of the headless interface
     * spec): a closed proof is {@link ResultStatus#CLOSED}; an unclosed proof is
     * {@link ResultStatus#TIMED_OUT} iff the run requested a timeout and the measured search time
     * reached it, otherwise {@link ResultStatus#OPEN}.
     * <p>
     * The stop condition's own message (accessible via {@code ProofSearchInformation.reason()})
     * does not distinguish a timeout from having reached the maximal number of rule applications,
     * so the classification relies on the measured elapsed time instead.
     *
     * @param closed whether all goals of the proof are closed
     * @param timeoutMs the requested proof-search timeout in milliseconds ({@code 0} = none)
     * @param elapsedMs the measured wall-clock time of the proof search in milliseconds
     * @return the final status of the contract
     */
    static ResultStatus classifyStatus(boolean closed, long timeoutMs, long elapsedMs) {
        if (closed) {
            return ResultStatus.CLOSED;
        }
        return timeoutMs > 0 && elapsedMs >= timeoutMs ? ResultStatus.TIMED_OUT
                : ResultStatus.OPEN;
    }

    private static long elapsedMs(long startNanos) {
        return TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - startNanos);
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
