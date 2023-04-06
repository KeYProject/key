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
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Proof slicer: constructs a new proof based on the original proof by omitting some steps that
 * are not required to complete the proof (as indicated by the provided analysis results).
 *
 * @author Arne Keller
 */
public final class SlicingProofReplayer extends IntermediateProofReplayer {
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SlicingProofReplayer.class);

    /**
     * The proof to slice.
     */
    private final Proof originalProof;
    /**
     * A proof saver of the original proof. Used to save and reload the initial proof obligation.
     */
    private final OutputStreamProofSaver originalProofSaver;
    /**
     * The proof slice created by the slicer.
     */
    private final Proof proof;
    /**
     * The analysis results used to construct the proof slice.
     */
    private final AnalysisResults results;
    /**
     * Mapping of steps that use a dynamically added rule.
     * If step A uses a rule added by step B, this map will save: step index of A -> step index of B
     */
    private final Map<Integer, Integer> stepIndexToDynamicRule;
    /**
     * Mapping of step indices (in the original proof) to the ifInsts of that step.
     */
    private final Map<Integer, Set<PosInOccurrence>> stepIdxToIfInsts;
    /**
     * Mapping of step indices (in the original proof) to the formula that step matched on.
     */
    private final Map<Integer, PosInOccurrence> stepIdxToPos;
    /**
     * Mapping of nodes in the new proof to step indices in the original proof.
     */
    private final Map<Node, Integer> newStepsToStepIndices = new IdentityHashMap<>();
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
     * @param problemLoader problem loader
     * @param originalProof proof to slice
     * @param proof resulting proof slice
     * @param results analysis results
     * @param progressMonitor progress monitor (may be null)
     */
    private SlicingProofReplayer(AbstractProblemLoader problemLoader, Proof originalProof,
            Proof proof, AnalysisResults results, ProgressMonitor progressMonitor) {
        super(problemLoader, proof);
        this.originalProof = originalProof;
        this.originalProofSaver = new OutputStreamProofSaver(originalProof);
        this.proof = proof;
        this.results = results;
        this.progressMonitor = progressMonitor;

        stepIndexToDynamicRule = results.usefulSteps.stream()
                .filter(node -> node.getAppliedRuleApp() != null
                        && node.getAppliedRuleApp().rule() instanceof Taclet
                        && ((Taclet) node.getAppliedRuleApp().rule()).getAddedBy() != null)
                .map(node -> new Pair<>(node.getStepIndex(),
                    ((Taclet) node.getAppliedRuleApp().rule()).getAddedBy().getStepIndex()))
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        stepIdxToIfInsts = results.usefulSteps.stream()
                .filter(node -> node.getAppliedRuleApp() != null)
                .map(node -> new Pair<>(node.getStepIndex(),
                    DependencyTracker.ifInstsOfRuleApp(node.getAppliedRuleApp(), node)))
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        stepIdxToPos = results.usefulSteps.stream()
                .filter(node -> node.getAppliedRuleApp() != null)
                .map(node -> new Pair<>(node.getStepIndex(),
                    node.getAppliedRuleApp().posInOccurrence()))
                .filter(it -> it.second != null)
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
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

        return new SlicingProofReplayer(problemLoader, originalProof, proof, results,
            progressMonitor);
    }

    /**
     * Slice the previously provided proof and save the result in a new temporary file.
     *
     * @return path to temporary proof file
     * @throws BuiltInConstructionException on error during slice construction
     * @throws IOException on error during proof saving
     */
    public File slice()
            throws BuiltInConstructionException, IOException {
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
            newStepsToStepIndices.put(openGoal.node(), node.getStepIndex());

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
     * Re-apply the provided node of the original proof on the goal in the new proof.
     *
     * @param node original proof node to re-apply
     * @param openGoal open goal to apply the proof node on
     * @return the new goals added by this rule application
     * @throws BuiltInConstructionException on error
     */
    private ImmutableList<Goal> reApplyRuleApp(Node node, Goal openGoal)
            throws BuiltInConstructionException {
        RuleApp ruleApp = node.getAppliedRuleApp();
        ImmutableList<Goal> nextGoals;
        if (ruleApp.rule() instanceof BuiltInRule) {
            IBuiltInRuleApp builtInRuleApp = constructBuiltinApp(node, openGoal);
            if (!builtInRuleApp.complete()) {
                builtInRuleApp = builtInRuleApp.tryToInstantiate(openGoal);
            }
            nextGoals = openGoal.apply(builtInRuleApp);
        } else if (ruleApp.rule() instanceof Taclet) {
            nextGoals = openGoal.apply(constructTacletApp(node, openGoal));
        } else {
            throw new IllegalStateException(
                "can only slice proofs that use built-ins and taclets");
        }
        return nextGoals;
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

    /**
     * Construct a built-in based on the step in the original proof.
     *
     * @param originalStep step in original proof
     * @param currGoal open goal in proof slice
     * @return built-in rule app
     * @throws BuiltInConstructionException on error
     */
    private IBuiltInRuleApp constructBuiltinApp(Node originalStep, Goal currGoal)
            throws BuiltInConstructionException {
        final RuleApp ruleApp = originalStep.getAppliedRuleApp();
        final String ruleName = ruleApp.rule().displayName();

        Contract currContract = null;
        ImmutableList<PosInOccurrence> builtinIfInsts = null;

        // Load contracts, if applicable
        if (ruleApp.rule() instanceof UseOperationContractRule
                || ruleApp.rule() instanceof UseDependencyContractRule) {
            RuleJustification justification = originalProof.getInitConfig().getJustifInfo()
                    .getJustification(ruleApp, originalProof.getServices());
            currContract = proof.getServices().getSpecificationRepository()
                    .getContractByName(
                        ((RuleJustificationBySpec) justification).getSpec().getName());
        }

        // Load ifInsts, if applicable
        builtinIfInsts = ImmutableSLList.nil();
        for (PosInOccurrence oldFormulaPio : stepIdxToIfInsts.get(originalStep.getStepIndex())) {
            PosInOccurrence newFormula = findInNewSequent(oldFormulaPio, currGoal.sequent());
            if (newFormula == null) {
                throw new IllegalStateException(String.format(
                    "did not locate built-in ifInst during slicing @ rule name %s, serial nr %d",
                    ruleName, originalStep.serialNr()));
            }
            builtinIfInsts = builtinIfInsts.append(newFormula);
        }

        if (RuleAppSMT.rule.displayName().equals(ruleName)) {
            return RuleAppSMT.rule.createApp(null, proof.getServices());
        }

        IBuiltInRuleApp ourApp = null;
        PosInOccurrence pos = null;

        if (stepIdxToPos.get(originalStep.getStepIndex()) != null) { // otherwise we have no pos
            PosInOccurrence oldPos = stepIdxToPos.get(originalStep.getStepIndex());
            pos = findInNewSequent(oldPos, currGoal.sequent());
            if (pos == null) {
                LOGGER.error("failed to find new formula @ built-in rule name {}, serial nr {}",
                    ruleName, originalStep.serialNr());
            }
        }

        if (currContract != null) {
            AbstractContractRuleApp contractApp = null;

            BuiltInRule useContractRule;
            if (currContract instanceof OperationContract) {
                useContractRule = UseOperationContractRule.INSTANCE;
                contractApp = (((UseOperationContractRule) useContractRule)
                        .createApp(pos)).setContract(currContract);
            } else {
                useContractRule = UseDependencyContractRule.INSTANCE;
                contractApp = (((UseDependencyContractRule) useContractRule)
                        .createApp(pos)).setContract(currContract);
            }

            if (contractApp.check(currGoal.proof().getServices()) == null) {
                throw new BuiltInConstructionException(
                    "Cannot apply contract: " + currContract);
            } else {
                ourApp = contractApp;
            }

            if (builtinIfInsts != null) {
                ourApp = ourApp.setIfInsts(builtinIfInsts);
            }
            return ourApp;
        }

        final ImmutableSet<IBuiltInRuleApp> ruleApps = collectAppsForRule(
            ruleName, currGoal, pos);
        if (ruleApps.size() != 1) {
            if (ruleApps.size() < 1) {
                throw new BuiltInConstructionException(
                    ruleName + " is missing. Most probably the binary "
                        + "for this built-in rule is not in your path or "
                        + "you do not have the permission to execute it.");
            } else {
                throw new BuiltInConstructionException(
                    ruleName + ": found " + ruleApps.size()
                        + " applications. Don't know what to do !\n" + "@ "
                        + pos);
            }
        }
        ourApp = ruleApps.iterator().next();
        if (ourApp instanceof OneStepSimplifierRuleApp) {
            ((OneStepSimplifierRuleApp) ourApp).restrictAssumeInsts(builtinIfInsts);
        }
        return ourApp;
    }

    /**
     * Construct a new taclet application based on a step in the original proof
     *
     * @param originalStep step in original proof
     * @param currGoal open goal in proof slice
     * @return new taclet app equivalent to {@code originalStep}
     */
    private TacletApp constructTacletApp(Node originalStep, Goal currGoal) {

        final String tacletName = originalStep.getAppliedRuleApp().rule().name().toString();

        TacletApp ourApp = null;
        PosInOccurrence pos = null;

        Taclet t = proof.getInitConfig()
                .lookupActiveTaclet(new Name(tacletName));
        if (t == null) {
            if (stepIndexToDynamicRule.containsKey(originalStep.getStepIndex())) {
                int idx = stepIndexToDynamicRule.get(originalStep.getStepIndex());
                // find the correct taclet
                boolean done = false;
                for (NoPosTacletApp partialApp : currGoal.indexOfTaclets()
                        .getPartialInstantiatedApps()) {
                    if (newStepsToStepIndices.get(partialApp.taclet().getAddedBy()) == idx) {
                        ourApp = partialApp;
                        done = true;
                        break;
                    }
                }
                if (!done) {
                    throw new IllegalStateException(
                        "slicer failed to find dynamically added taclet");
                }
            } else {
                ourApp = currGoal.indexOfTaclets().lookup(tacletName);
            }
        } else {
            ourApp = NoPosTacletApp.createNoPosTacletApp(t);
        }
        if (ourApp == null) {
            throw new IllegalStateException("slicer failed to find taclet with name " + tacletName);
        }

        Services services = proof.getServices();

        PosInOccurrence oldPos = originalStep.getAppliedRuleApp().posInOccurrence();
        if (oldPos != null) { // otherwise we have no pos
            pos = findInNewSequent(oldPos, currGoal.sequent());
            if (pos == null) {
                throw new IllegalStateException(String.format(
                    "failed to find new formula @ %s (serial nr %d)", tacletName,
                    originalStep.serialNr()));
            }
            ourApp = ((NoPosTacletApp) ourApp).matchFind(pos, services);
            ourApp = ourApp.setPosInOccurrence(pos, services);
        }

        RuleApp app = originalStep.getAppliedRuleApp();
        assert app instanceof TacletApp;
        TacletApp tacletApp = (TacletApp) app;
        SVInstantiations instantantions = tacletApp.instantiations();
        ourApp = constructInsts(ourApp, currGoal,
            originalProofSaver.getInterestingInstantiations(instantantions), services);

        ImmutableList<IfFormulaInstantiation> ifFormulaList = ImmutableSLList.nil();
        List<Pair<PosInOccurrence, Boolean>> oldFormulas =
            stepIdxToIfInsts.get(originalStep.getStepIndex()).stream()
                    .map(x -> new Pair<>(x, true))
                    .collect(Collectors.toList());
        if (tacletApp instanceof PosTacletApp) {
            PosTacletApp posTacletApp = (PosTacletApp) tacletApp;
            if (posTacletApp.ifFormulaInstantiations() != null) {
                for (IfFormulaInstantiation x : posTacletApp.ifFormulaInstantiations()) {
                    if (x instanceof IfFormulaInstDirect) {
                        oldFormulas.add(new Pair<>(new PosInOccurrence(x.getConstrainedFormula(),
                            PosInTerm.getTopLevel(), true), false));
                    }
                }
            }
        }
        for (Pair<PosInOccurrence, Boolean> oldFormulaPioSpec : oldFormulas) {
            PosInOccurrence oldFormulaPio = oldFormulaPioSpec.first;
            PosInOccurrence newPio = findInNewSequent(oldFormulaPio, currGoal.sequent());
            if (newPio == null) {
                throw new IllegalStateException(String.format(
                    "did not locate ifInst during slicing @ rule name %s, serial nr %d",
                    tacletName,
                    originalStep.serialNr()));
            }
            if (oldFormulaPioSpec.second) {
                ifFormulaList = ifFormulaList.append(
                    new IfFormulaInstSeq(currGoal.sequent(), oldFormulaPio.isInAntec(),
                        newPio.sequentFormula()));
            } else {
                ifFormulaList = ifFormulaList.append(
                    new IfFormulaInstDirect(newPio.sequentFormula()));
            }
        }

        ourApp = ourApp.setIfFormulaInstantiations(ifFormulaList, services);
        if (ourApp == null) {
            throw new IllegalStateException(String.format(
                "slicing encountered null rule app of %s after instantiating ifInsts", tacletName));
        }

        if (!ourApp.complete()) {
            ourApp = ourApp.tryToInstantiate(proof.getServices());
        }

        return ourApp;
    }

    /**
     * Try to find the provided formula in the provided sequent,
     * using {@link org.key_project.util.EqualsModProofIrrelevancy} to check for equality.
     *
     * @param oldPos formula to look for
     * @param newSequent sequent
     * @return the formula in the sequent, or null if not found
     */
    private PosInOccurrence findInNewSequent(PosInOccurrence oldPos, Sequent newSequent) {
        SequentFormula oldFormula = oldPos.sequentFormula();
        Semisequent semiSeq = oldPos.isInAntec() ? newSequent.antecedent()
                : newSequent.succedent();
        for (SequentFormula newFormula : semiSeq.asList()) {
            if (newFormula.equalsModProofIrrelevancy(oldFormula)) {
                return oldPos.replaceConstrainedFormula(newFormula);
            }
        }
        return null;
    }
}
