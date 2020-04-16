package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.check.dependency.DependencyNode;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.Logger;

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

/**
 * This class serves as a container for the data given to and returned by a Checker. It contains:
 *      - the consistency result (boolean)
 *      - the file tree
 *      - information about the proofs (basically a table)
 *      - the dependency graph
 *      - additional raw text messages
 *
 * Note: This is a mutable data container!
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

    ////////////////////////////////// results from dependency checker

    private DependencyGraph dependencyGraph;

    /** unproven external (user provided) contracts */
    private final List<Contract> unprovenExternal = new ArrayList<>();

    /** unproven internal contracts (from classes shipped with KeY) */
    private final List<Contract> unprovenInternal = new ArrayList<>();

    /** fully proven contracts (including all dependencies) */
    private final List<Contract> proven = new ArrayList<>();

    /** proven contracts with lemmas/dependencies left unproven */
    private final List<Contract> lemmasLeft = new ArrayList<>();

    private final List<DependencyNode> missingMby = new ArrayList<>();
    private final List<DependencyGraph.SCC> illegalCycles = new ArrayList<>();


    public void addUnprovenContract(Contract c, boolean internal) {
        if (internal) {
            unprovenInternal.add(c);
        } else {
            unprovenExternal.add(c);
        }
    }

    ////////////////////////////////// results from settings checker

    // all choice names that are used in the settings of at least one proof
    private final SortedSet<String> choiceNames = new TreeSet<>();

    public SortedSet<String> getChoiceNames() {
        return choiceNames;
    }

    public void addChoiceName(String name) {
        choiceNames.add(name);
    }

    private final Map<HashMap<String, String>, Integer> choices2Id = new HashMap<>();

    public void addChoices(HashMap<String, String> choices, int id) {
        choices2Id.put(choices, id);
    }

    public Map<HashMap<String, String>, Integer> getChoices2Id() {
        return choices2Id;
    }

    //////////////////////////////////

    // TODO: default value
    private boolean consistent = false;
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

    public class ProofEntry {
        public boolean loaded = false;
        public BranchNodeIntermediate rootNode;
        public Proof proof;
        public KeYUserProblemFile envInput;
        public ProblemInitializer problemInitializer;
        public Path proofFile;
        public Contract contract;
        public URL sourceFile;
        public String shortSrc;
        public AbstractProblemLoader.ReplayResult replayResult;

        public Integer settingsId() {
            HashMap<String, String> cs = proof.getSettings().getChoiceSettings().getDefaultChoices();
            Integer lookup = choices2Id.get(cs);
            if (lookup != null) {
                return lookup;      // found exact match
            }
            /*
            // no exact match -> look for equal settings
            for (ChoiceSettings s : choices2Id.keySet()) {
                if (settingsEqual(s, cs)) {
                    // found matching settings
                    return choices2Id.get(s);
                }
            }
            */
            return null;            // should not happen
        }
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

    public boolean isConsistent() {
        return consistent;
    }

    public void setConsistent(boolean consistent) {
        this.consistent = consistent;
    }

    public void setPbh(ProofBundleHandler pbh) {
        this.pbh = pbh;
    }

    public void setFileTree(PathNode fileTree) {
        this.fileTree = fileTree;
    }

    public void setDependencyGraph(DependencyGraph dependencyGraph) {
        this.dependencyGraph = dependencyGraph;
    }
}
