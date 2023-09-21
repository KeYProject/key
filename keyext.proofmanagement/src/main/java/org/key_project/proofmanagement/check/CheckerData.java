/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.net.URL;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;

import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.Logger;
import org.key_project.proofmanagement.io.ProofBundleHandler;

/**
 * This container serves for accumulating data given to checkers and results returned by them.
 *
 * @author Wolfram Pfeifer
 */
public final class CheckerData implements Logger {

    public CheckerData(LogLevel minLogLevel) {
        this.minLogLevel = minLogLevel;
    }

    public String getCheckDate() {
        return checkDate;
    }

    private final String checkDate = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss")
            .format(LocalDateTime.now());

    private final Map<String, String> checks = new HashMap<>();

    /** minimum log level: all messages with a smaller LogLevel will be suppressed */
    private final LogLevel minLogLevel;

    private final List<String> messages = new ArrayList<>();

    // TODO: side effects: may be changed by checkers (e.g. remove paths of taclet proofs)
    private List<Path> proofPaths;

    ////////////////////////////////// results from dependency checker

    private DependencyGraph dependencyGraph;

    ////////////////////////////////// results from missing proofs checker

    public Set<Contract> getContractsWithoutProof() {
        return contractsWithoutProof;
    }

    /** user provided contracts for which no proof exists */
    private final Set<Contract> contractsWithoutProof = new HashSet<>();

    /** internal contracts (from classes shipped with KeY) without a proof */
    private final Set<Contract> internalContractsWithoutProof = new HashSet<>();

    public void addContractWithoutProof(Contract c, boolean internal) {
        if (internal) {
            internalContractsWithoutProof.add(c);
        } else {
            contractsWithoutProof.add(c);
        }
        // if there is a proof for this contract, set its state to unproven
        ProofEntry entry = getProofEntryByContract(c);
        if (entry != null) {
            entry.dependencyState = DependencyState.UNPROVEN_DEP;
        }
    }

    ////////////////////////////////// results from settings checker

    /** all choice names that occur in at least one settings object of a proof */
    private final SortedSet<String> choiceNames = new TreeSet<>();

    public SortedSet<String> getChoiceNames() {
        return choiceNames;
    }

    /** choices used as reference (mapped to their corresponding id) */
    private final Map<Map<String, String>, Integer> referenceChoices = new HashMap<>();

    /** mapping from choices to the reference id */
    private final Map<Map<String, String>, Integer> choices2Id = new HashMap<>();

    /**
     * Adds a choices map to the map of reference choices. The newly added map gets the next free
     * id. Use only if it is known that the given choices object is not yet in the map!
     * In addition, an entry in the map for id lookup is added ({@link #addChoices(Map)} is
     * called).
     *
     * @param choices the reference choices to add
     */
    public void addReferenceChoices(Map<String, String> choices) {
        int nextId = referenceChoices.size();
        referenceChoices.putIfAbsent(choices, nextId);
        // add an entry in the map for id lookup
        addChoices(choices);
        // ensure that all keys are in set
        choiceNames.addAll(choices.keySet());
    }

    /**
     * Adds a mapping to a reference choices id for the given choices. Use only if an equal
     * reference choices object has already been added via {@link #addReferenceChoices(Map)}.
     *
     * @param choices the choices to add a mapping
     */
    public void addChoices(Map<String, String> choices) {
        // if no id is found, a NPE is thrown
        int referenceId = referenceChoices.get(choices);
        choices2Id.putIfAbsent(choices, referenceId);
    }

    public Map<Map<String, String>, Integer> getChoices2Id() {
        return choices2Id;
    }

    /**
     * Prepare short names for concise display of ChoiceSettings:
     * In the values, everything up to and including the colon is removed.
     *
     * @return a map of choice settings to reference id, using short choice values
     */
    public Map<Map<String, String>, Integer> getShortChoices2Id() {

        Map<Map<String, String>, Integer> res = new HashMap<>();

        // copy outer mapping
        for (Map.Entry<Map<String, String>, Integer> inner : choices2Id.entrySet()) {
            // in inner mapping, replace values by short names
            Map<String, String> copy = new HashMap<>();
            for (Map.Entry<String, String> s : inner.getKey().entrySet()) {
                // remove everything up to and including the colon
                String val = s.getValue();
                copy.put(s.getKey(), val.substring(val.indexOf(':') + 1));
            }
            res.put(copy, inner.getValue());
        }
        return res;
    }

    //////////////////////////////////

    private LoadingState srcLoadingState = LoadingState.UNKNOWN;
    // we use methods to determine these states on the fly
    // private LoadingState proofLoadingState = LoadingState.UNKNOWN;
    // private ReplayState replayState = ReplayState.UNKNOWN;
    // private DependencyState depState = DependencyState.UNKNOWN;
    private SettingsState settingsState = SettingsState.UNKNOWN;
    private GlobalState globalState = GlobalState.UNKNOWN;

    private ProofBundleHandler pbh;
    private PathNode fileTree;
    private final List<ProofEntry> proofEntries = new ArrayList<>();
    private SLEnvInput slenv;

    public SLEnvInput getSlenv() {
        return slenv;
    }

    public void setSlenv(SLEnvInput slenv) {
        this.slenv = slenv;
    }

    // we rely on the order of the enums (from worst to best)!!!
    public enum GlobalState {
        ERROR,
        UNKNOWN,
        CLOSED,
        OPEN
    }

    public enum SettingsState {
        UNKNOWN,
        INCONSISTENT,
        CONSISTENT
    }

    public enum ReplayState {
        ERROR("\u2718"), // cross/xmark
        UNKNOWN("?"),
        SUCCESS("\u2714"); // checkmark

        private final String shortStr;

        ReplayState(String shortStr) {
            this.shortStr = shortStr;
        }

        @Override
        public String toString() {
            return shortStr;
        }
    }

    public enum LoadingState {
        ERROR("\u2718"), // cross/xmark
        UNKNOWN("?"),
        SUCCESS("\u2714"); // checkmark

        private final String shortStr;

        LoadingState(String shortStr) {
            this.shortStr = shortStr;
        }

        @Override
        public String toString() {
            return shortStr;
        }
    }

    public enum DependencyState {
        UNKNOWN("?"),
        ILLEGAL_CYCLE("cycle"),
        UNPROVEN_DEP("open dep."),
        OK("\u2714"); // checkmark

        private final String shortStr;

        DependencyState(String shortStr) {
            this.shortStr = shortStr;
        }

        @Override
        public String toString() {
            return shortStr;
        }
    }

    public enum ProofState {
        UNKNOWN("?"),
        OPEN("open"),
        CLOSED("closed");

        private final String shortStr;

        ProofState(String shortStr) {
            this.shortStr = shortStr;
        }

        @Override
        public String toString() {
            return shortStr;
        }
    }

    public class ProofEntry {
        public LoadingState loadingState = LoadingState.UNKNOWN;
        public ReplayState replayState = ReplayState.UNKNOWN;
        public DependencyState dependencyState = DependencyState.UNKNOWN;
        public ProofState proofState = ProofState.UNKNOWN;

        public boolean replaySuccess() {
            return replayState == ReplayState.SUCCESS;
        }

        public Path proofFile;
        public KeYUserProblemFile envInput;
        public ProblemInitializer problemInitializer;
        public Proof proof;

        public Contract contract;
        public URL sourceFile;
        public String shortSrc;
        public IntermediatePresentationProofFileParser.Result parseResult;
        public AbstractProblemLoader.ReplayResult replayResult;

        public Integer settingsId() {
            return choices2Id.get(proof.getSettings().getChoiceSettings().getDefaultChoices());
        }
    }

    public ProofEntry getProofEntryByContract(Contract contract) {
        for (ProofEntry p : proofEntries) {
            if (p.contract.equals(contract)) {
                return p;
            }
        }
        return null;
    }

    // TODO: equals method of ChoiceSettings (may be impossible, since listeners are not compared)
    private static boolean settingsEqual(ChoiceSettings a, ChoiceSettings b) {
        // all currently selected choices equal?
        return a.getDefaultChoices().equals(b.getDefaultChoices());
    }

    public void addCheck(String checkName) {
        checks.put(checkName, checkName);
    }

    public Map<String, String> getChecks() {
        return checks;
    }

    @Override
    public void print(String message) {
        print(LogLevel.DEFAULT, message);
    }

    @Override
    public void print(LogLevel level, String message) {
        // suppress message if level is smaller than current log level
        if (level.compareTo(minLogLevel) >= 0) {
            // for multiline strings, every line should have correct prefix
            String[] lines = message.split("\\r?\\n");
            for (String l : lines) {
                messages.add(level + l);
                System.out.println(level + l);
            }
        }
    }

    public List<String> getMessages() {
        return messages;
    }

    public PathNode getFileTree() {
        return fileTree;
    }

    public List<ProofEntry> getProofEntries() {
        return proofEntries;
    }

    public DependencyGraph getDependencyGraph() {
        return dependencyGraph;
    }

    public ProofBundleHandler getPbh() {
        return pbh;
    }

    public void setSrcLoadingState(LoadingState srcLoadingState) {
        this.srcLoadingState = srcLoadingState;
    }

    private LoadingState getSrcLoadingState() {
        return srcLoadingState;
    }

    private LoadingState determineProofLoadingState() {
        LoadingState worst = LoadingState.SUCCESS;
        for (ProofEntry entry : proofEntries) {
            if (entry.loadingState.compareTo(worst) < 0) {
                // found proof with worse state
                worst = entry.loadingState;
            }
        }
        return worst;
    }

    private ReplayState determineReplayState() {
        ReplayState worst = ReplayState.SUCCESS;
        for (ProofEntry entry : proofEntries) {
            if (entry.replayState.compareTo(worst) < 0) {
                // found proof with worse state
                worst = entry.replayState;
            }
        }
        return worst;
    }

    private DependencyState determineDependencyState() {
        DependencyState worst = DependencyState.OK;
        for (ProofEntry entry : proofEntries) {
            if (entry.dependencyState.compareTo(worst) < 0) {
                // found proof with worse state
                worst = entry.dependencyState;
            }
        }
        return worst;
    }

    private SettingsState getSettingsState() {
        return settingsState;
    }

    public void setSettingsState(SettingsState settingsState) {
        this.settingsState = settingsState;
    }

    public void updateGlobalState() {
        // we don't want to call these methods too often, since they iterate the proofs
        LoadingState srcLoadingState = getSrcLoadingState();
        LoadingState proofLoadingState = determineProofLoadingState();
        ReplayState replayState = determineReplayState();
        DependencyState depState = determineDependencyState();
        SettingsState settingsState = getSettingsState();

        if (srcLoadingState == LoadingState.ERROR
                || proofLoadingState == LoadingState.ERROR
                || replayState == ReplayState.ERROR) {
            globalState = GlobalState.ERROR; // error
        } else if (srcLoadingState == LoadingState.UNKNOWN
                || proofLoadingState == LoadingState.UNKNOWN
                || replayState == ReplayState.UNKNOWN
                || settingsState == SettingsState.UNKNOWN
                || depState == DependencyState.UNKNOWN) {
            globalState = GlobalState.UNKNOWN; // unknown
        } else if (srcLoadingState == LoadingState.SUCCESS
                && proofLoadingState == LoadingState.SUCCESS
                && replayState == ReplayState.SUCCESS
                && settingsState == SettingsState.CONSISTENT
                && depState == DependencyState.OK
                && contractsWithoutProof.isEmpty()
                && proofEntries.stream().allMatch(p -> p.proofState == ProofState.CLOSED)) {
            globalState = GlobalState.CLOSED; // closed
        } else {
            globalState = GlobalState.OPEN; // open
        }
    }

    public int bundleProofCount() {
        return provenCount() + lemmaLeftCount() + unprovenCount();
    }

    // count proofs that are closed but have unproven dependencies
    public int lemmaLeftCount() {
        int count = 0;
        for (ProofEntry entry : proofEntries) {
            if (entry.proofState == ProofState.CLOSED
                    && entry.dependencyState == DependencyState.UNPROVEN_DEP) {
                count++;
            }
        }
        return count;
    }

    public boolean hasLemmaLeftContracts() {
        return lemmaLeftCount() != 0;
    }

    // count proofs that are closed and have all dependencies proven
    public int provenCount() {
        int count = 0;
        for (ProofEntry entry : proofEntries) {
            if (entry.proofState == ProofState.CLOSED
                    && entry.dependencyState != DependencyState.UNPROVEN_DEP
                    && entry.dependencyState != DependencyState.ILLEGAL_CYCLE) {
                count++;
            }
        }
        return count;
    }

    public boolean hasProvenContracts() {
        return provenCount() != 0;
    }

    // count proofs that are open, unknown (due to error), or have cyclic dependencies
    public int unprovenCount() {
        int count = 0;
        for (ProofEntry entry : proofEntries) {
            // proofs that are closed but have illegal cyclic dependencies are considered unproven!
            if (entry.proofState != ProofState.CLOSED
                    || (entry.dependencyState == DependencyState.ILLEGAL_CYCLE)) {
                count++;
            }
        }
        // count in contracts defined inside bundle that have no proof
        count += contractsWithoutProof.size();
        return count;
    }

    public boolean hasUnprovenContracts() {
        return unprovenCount() != 0;
    }

    public GlobalState getGlobalState() {
        updateGlobalState();
        return globalState;
    }

    public void setPbh(ProofBundleHandler pbh) {
        this.pbh = pbh;
    }

    public List<Path> getProofPaths() throws ProofManagementException {
        if (proofPaths == null) {
            proofPaths = pbh.getProofFiles();
        }
        return proofPaths;
    }

    public void setFileTree(PathNode fileTree) {
        this.fileTree = fileTree;
    }

    public void setDependencyGraph(DependencyGraph dependencyGraph) {
        this.dependencyGraph = dependencyGraph;
    }
}
