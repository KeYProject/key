/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.replay.AbstractProofReplayer;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.util.collection.ImmutableList;

/**
 * Proof slicer: constructs a new proof based on the original proof by omitting some steps that
 * are not required to complete the proof (as indicated by the provided analysis results).
 *
 * @author Arne Keller
 */
public final class SlicingProofReplayer extends AbstractProofReplayer {
    /**
     * The proof to slice.
     */
    private final Proof originalProof;
    /**
     * The proof slice created by the slicer.
     */
    private final Proof proof;
    /**
     * The analysis results used to construct the proof slice.
     */
    private final AnalysisResults results;
    /**
     * Mapping: step index (original proof) -> list of steps to apply before that step.
     */
    private final Map<Integer, List<Node>> branchStacks;
    /**
     * Progress monitor, used to report slicing progress. May be null.
     */
    private final ProgressMonitor progressMonitor;

    /**
     * Construct a new slicing proof replayer.
     *
     * @param originalProof proof to slice
     * @param proof resulting proof slice
     * @param results analysis results
     * @param progressMonitor progress monitor (may be null)
     */
    private SlicingProofReplayer(Proof originalProof,
            Proof proof, AnalysisResults results, ProgressMonitor progressMonitor) {
        super(originalProof, proof);
        this.originalProof = originalProof;
        this.proof = proof;
        this.results = results;
        this.progressMonitor = progressMonitor;

        branchStacks = results.branchStacks.entrySet()
                .stream().map(entry -> new Pair<>(
                    entry.getKey().getStepIndex(),
                    entry.getValue()))
                .collect(Collectors.toMap(p -> p.first, p -> p.second));
    }

    /**
     * Constructs a new {@link SlicingProofReplayer}.
     * Call {@link #slice()} on the result to compute the sliced proof and save it into a temporary
     * file.
     *
     * @param control the problem loader control (used to reload the initial proof obligation)
     * @param originalProof the proof to slice
     * @param results the analysis results used to determine the proof slice
     * @param progressMonitor monitor for slicing progress
     * @return a slicing proof replayer for the provided parameters
     * @throws IOException if the original proof obligation could not be saved in a temporary file
     * @throws ProofInputException if there was an issue loading the original proof obligation
     * @throws ProblemLoaderException if there was an issue loading the original proof obligation
     */
    public static SlicingProofReplayer constructSlicer(ProblemLoaderControl control,
            Proof originalProof,
            AnalysisResults results,
            ProgressMonitor progressMonitor)
            throws IOException, ProofInputException, ProblemLoaderException {
        boolean loadInUI = MainWindow.hasInstance();
        if (loadInUI) {
            MainWindow.getInstance().setStatusLine(
                "Preparing proof slicing", 2);
        }
        Path tmpFile = Files.createTempFile("proof", ".proof");
        originalProof.saveProofObligationToFile(tmpFile.toFile());
        if (progressMonitor != null) {
            progressMonitor.setProgress(1);
        }

        String bootClassPath = originalProof.getEnv().getJavaModel().getBootClassPath();
        AbstractProblemLoader problemLoader = new SingleThreadProblemLoader(
            tmpFile.toFile(),
            originalProof.getEnv().getJavaModel().getClassPathEntries(),
            bootClassPath != null ? new File(bootClassPath) : null,
            null,
            originalProof.getEnv().getInitConfigForEnvironment().getProfile(),
            false,
            control, false, null);
        problemLoader.load();
        if (progressMonitor != null) {
            progressMonitor.setProgress(2);
        }
        Files.delete(tmpFile);
        Proof proof = problemLoader.getProof();

        return new SlicingProofReplayer(originalProof, proof, results,
            progressMonitor);
    }

    /**
     * Slice the previously provided proof and save the result in a new temporary file.
     *
     * @return path to temporary proof file
     * @throws de.uka.ilkd.key.proof.io.IntermediateProofReplayer.BuiltInConstructionException on
     *         error during slice construction
     * @throws IOException on error during proof saving
     */
    public File slice()
            throws IntermediateProofReplayer.BuiltInConstructionException, IOException {
        boolean loadInUI = MainWindow.hasInstance();
        if (loadInUI) {
            MainWindow.getInstance().setStatusLine(
                "Slicing proof", results.usefulSteps.size());
        }

        // queue of open goals in the new proof
        Deque<Goal> openGoals = new ArrayDeque<>();
        openGoals.addLast(proof.openGoals().head());
        // queue of nodes in the original proof
        // second pair field indicates whether the next steps of the node should be added to the
        // queue (false if the step is part of a branch stack)
        Deque<Pair<Node, Boolean>> stepsToApply = new ArrayDeque<>();
        stepsToApply.addLast(new Pair<>(originalProof.root(), true));
        Map<Node, Boolean> appliedSteps = new IdentityHashMap<>();

        while (!stepsToApply.isEmpty()) {
            Pair<Node, Boolean> p = stepsToApply.removeFirst();
            Node node = p.first;
            boolean addChildren = p.second;
            // check for a branch stack, and add those steps to the queue
            List<Node> stackContent = branchStacks.remove(node.getStepIndex());
            if (stackContent != null) {
                stepsToApply.addFirst(p);
                for (int i = stackContent.size() - 1; i >= 0; i--) {
                    stepsToApply.addFirst(new Pair<>(stackContent.get(i), false));
                }
                continue;
            }
            // add next step(s) to the queue
            if (addChildren) {
                for (int i = node.childrenCount() - 1; i >= 0; i--) {
                    stepsToApply.addFirst(new Pair<>(node.child(i), true));
                }
            }
            // only re-apply useful steps, and only re-apply each step once (relevant if this node
            // has been de-duplicated and was applied earlier as part of a branch stack)
            if (!results.usefulSteps.contains(node) || appliedSteps.containsKey(node)) {
                continue;
            }
            appliedSteps.put(node, true);
            if (loadInUI && progressMonitor != null) {
                progressMonitor.setProgress(appliedSteps.size());
            }
            Goal openGoal = openGoals.removeFirst();

            // copy over metadata
            Node newNode = openGoal.node();
            newNode.getNodeInfo().copyFrom(node);

            // re-apply rule
            RuleApp ruleApp = node.getAppliedRuleApp();
            if (ruleApp == null) {
                // open goal intentionally left open, go to next branch
                continue;
            }
            proof.getServices().getNameRecorder().setProposals(
                node.getNameRecorder().getProposals());

            ImmutableList<Goal> nextGoals = reApplyRuleApp(node, openGoal);
            for (Goal newGoal : nextGoals) {
                boolean closedGoal = newGoal.node().isClosed();
                if (!closedGoal) {
                    openGoals.addFirst(newGoal);
                }
            }
        }

        return saveProof(originalProof, proof);
    }

    /**
     * Save <code>proof</code> in a temporary directory with a reasonable filename.
     * Disposes the saved proof.
     *
     * @param currentProof the sliced proof
     * @param proof the proof slice
     * @return path to the saved proof slice
     * @throws IOException on I/O error
     */
    private File saveProof(Proof currentProof, Proof proof) throws IOException {
        Path tempDir = Files.createTempDirectory("KeYslice");
        String filename;
        if (currentProof.getProofFile() != null) {
            filename = MiscTools.removeFileExtension(currentProof.getProofFile().getName());
        } else {
            filename = MiscTools.removeFileExtension(currentProof.name().toString());
            // make sure that no special chars are in name (e.g., "Taclet: seqPerm ..." for taclet
            // proofs)
            filename = MiscTools.toValidFileName(filename);
        }
        int prevSlice = filename.indexOf("_slice");
        if (prevSlice != -1) {
            int sliceNr = Integer.parseInt(filename.substring(prevSlice + "_slice".length()));
            sliceNr++;
            filename = filename.substring(0, prevSlice) + "_slice" + sliceNr;
        } else {
            filename = filename + "_slice1";
        }
        filename = filename + ".proof";
        File tempFile = tempDir.resolve(filename).toFile();
        proof.saveToFile(tempFile);
        proof.dispose();
        return tempFile;
    }
}
