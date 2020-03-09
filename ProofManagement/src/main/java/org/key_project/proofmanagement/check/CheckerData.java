package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.util.java.IOUtil;

import java.net.URL;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
public final class CheckerData {

    public String getCheckDate() {
        return checkDate;
    }

    private final String checkDate = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss")
                                                      .format(LocalDateTime.now());

    private final Map<String, String> checks = new HashMap<>();

    private final List<String> messages = new ArrayList<>();

    // TODO: default value
    private boolean consistent = false;
    private ProofBundleHandler pbh;
    private PathNode fileTree;
    private List<ProofLine> proofLines;
    private DependencyGraph dependencyGraph;

    public static class ProofLine {
        public Proof proof;
        public EnvInput envInput;
        public ProblemInitializer problemInitializer;
        public Path proofFile;
        public Contract contract;
        public URL sourceFile;
        public String shortSrc;
        public AbstractProblemLoader.ReplayResult replayResult;
    }

    public void addCheck(String checkName) {
        checks.put(checkName, checkName);
    }

    public Map<String, String> getChecks() {
        return checks;
    }

    public void print(String message) {
        messages.add(message);
        System.out.println(message);
    }

    public List<String> getMessages() {
        return messages;
    }

    public PathNode getFileTree() {
        return fileTree;
    }

    public List<ProofLine> getProofLines() {
        return proofLines;
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

    public void setProofLines(List<ProofLine> proofLines) {
        this.proofLines = proofLines;
    }

    public void setDependencyGraph(DependencyGraph dependencyGraph) {
        this.dependencyGraph = dependencyGraph;
    }
}
