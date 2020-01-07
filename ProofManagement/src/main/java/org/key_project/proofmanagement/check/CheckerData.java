package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.Contract;
import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.io.ProofBundleHandler;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * This class serves as a container for the data given to and returned by a Checker. It contains:
 *      - the consistency result (boolean)
 *      - the file tree
 *      - information about the proofs (basically a table)
 *      - the dependency graph
 *      - additional raw text messages
 */
public class CheckerData {
    // TODO: default value
    private boolean consistent = false;

    private final ProofBundleHandler pbh;
    private final PathNode fileTree;
    private final List<ProofLine> proofLines;
    private final DependencyGraph dependencyGraph;
    private List<String> messages = new ArrayList<>();

    public static class ProofLine {
        public Proof proof;
        public Path proofFile;
        public Contract contract;
        public Path sourceFile;
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


    // TODO: Is there a better way to ensure that at most one of the "data fields" is set for a
    //  newly created CheckResult (e.g. setters with exceptions)?
    public CheckerData(ProofBundleHandler pbh, PathNode fileTree) {
        this(false, pbh, fileTree, null, null);
    }

    public CheckerData(ProofBundleHandler pbh, DependencyGraph dependencyGraph) {
        this(false, pbh, null, null, dependencyGraph);
    }
    public CheckerData(ProofBundleHandler pbh, List<ProofLine> proofLines) {
        this(false, pbh, null, proofLines, null);
    }

    public CheckerData(boolean consistent, ProofBundleHandler pbh) {
        this(consistent, pbh, null, null, null);
    }

    public CheckerData(boolean consistent, ProofBundleHandler pbh, PathNode fileTree,
                       List<ProofLine> proofLines, DependencyGraph dependencyGraph) {
        this.consistent = consistent;
        this.pbh = pbh;
        this.fileTree = fileTree;
        this.proofLines = proofLines;
        this.dependencyGraph = dependencyGraph;
    }

    public void addMessage(String message) {
        messages.add(message);
    }

    public void addMessages(List<String> otherMessages) {
        messages.addAll(otherMessages);
    }

    public boolean isConsistent() {
        return consistent;
    }

    public List<String> getMessages() {
        return messages;
    }

    public CheckerData join(CheckerData other) {
        boolean consistent = other.isConsistent() && isConsistent();
        // assert other.pbh == this.pbh;
        PathNode fileTree = join(other.fileTree);
        List<ProofLine> proofLines = join(other.proofLines);
        DependencyGraph dependencyGraph = join(other.dependencyGraph);

        CheckerData res = new CheckerData(consistent, pbh, fileTree, proofLines, dependencyGraph);
        res.addMessages(this.getMessages());
        res.addMessages(other.getMessages());
        return res;
    }

    private PathNode join(PathNode other) {
        if (fileTree != null && other != null) {
            throw new IllegalArgumentException("Error! Both file trees are non-null!");
        }
        return firstNonNull(fileTree, other);
    }

    private List<ProofLine> join(List<ProofLine> other) {
        if (proofLines != null && other != null) {
            throw new IllegalArgumentException("Error! Both proof tables are non-null!");
        }
        return firstNonNull(proofLines, other);
    }

    private DependencyGraph join(DependencyGraph other) {
        if (dependencyGraph != null && other != null) {
            throw new IllegalArgumentException("Error! Both dependency graphs are non-null!");
        }
        return firstNonNull(dependencyGraph, other);
    }

    public static <T> T firstNonNull(T a, T b) {
        return a != null ? a : b;
    }
}
