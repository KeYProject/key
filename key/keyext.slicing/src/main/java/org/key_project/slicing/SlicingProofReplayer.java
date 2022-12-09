package org.key_project.slicing;

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
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProgressMonitor;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Proof slicer: constructs a new proof based on the original proof by omitting some steps that
 * are not required to complete the proof (as indicated by the provided analysis results).
 *
 * @author Arne Keller
 */
public final class SlicingProofReplayer extends IntermediateProofReplayer {
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
     * Mapping of step indices (in the original proof) to nodes in the new proof.
     */
    private final Map<Integer, Node> stepIndexToNewSteps = new HashMap<>();
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
    private final ProgressMonitor progressMonitor;

    /**
     * Constructs a new {@link SlicingProofReplayer}.
     *
     * @param control the problem loader control (used to reload the initial proof obligation)
     * @param originalProof the proof to slice
     * @param results the analysis results used to determine the proof slice
     * @param progressMonitor monitor for slicing progress
     * @throws IOException if the original proof obligation could not be saved in a temporary file
     * @throws ProofInputException if there was an issue loading the original proof obligation
     * @throws ProblemLoaderException if there was an issue loading the original proof obligation
     */
    public static SlicingProofReplayer constructSlicer(ProblemLoaderControl control,
            Proof originalProof,
            AnalysisResults results,
            ProgressMonitor progressMonitor)
            throws IOException, ProofInputException, ProblemLoaderException {
        Path tmpFile = Files.createTempFile("proof", ".proof");
        originalProof.saveProofObligationToFile(tmpFile.toFile());

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
        Files.delete(tmpFile);
        Proof proof = problemLoader.getProof();

        return new SlicingProofReplayer(problemLoader, originalProof, proof, results,
            progressMonitor);
    }

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
                .map(node -> new Pair<>(node.getStepIndex(),
                    DependencyTracker.ifInstsOfRuleApp(node.getAppliedRuleApp(), node)))
                .collect(Collectors.toMap(it -> it.first, it -> it.second));
        stepIdxToPos = results.usefulSteps.stream()
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

    public File slice() throws TacletAppConstructionException, BuiltInConstructionException, IOException {
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
            List<Node> stackContent = branchStacks.get(node.getStepIndex());
            if (stackContent != null) {
                branchStacks.remove(node.getStepIndex());
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
            /*
             * if (node.getAppliedRuleApp() != null) {
             * LOGGER.info("executing original step {} (step index {})",
             * node.getAppliedRuleApp().rule().displayName(), node.stepIndex);
             * }
             */
            if (!results.usefulSteps.contains(node) || appliedSteps.containsKey(node)) {
                continue;
            }
            appliedSteps.put(node, true);
            if (loadInUI) {
                progressMonitor.setProgress(appliedSteps.size());
            }
            Goal openGoal = openGoals.removeFirst();
            newStepsToStepIndices.put(openGoal.node(), node.getStepIndex());

            // copy over metadata
            Node newNode = openGoal.node();
            newNode.setStepIndex(node.getStepIndex());
            newNode.getNodeInfo().copyFrom(node);
            proof.getServices().getNameRecorder().setProposals(
                node.getNameRecorder().getProposals());

            // re-apply rule
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
            stepIndexToNewSteps.put(node.getStepIndex(), openGoal.node().parent());
            for (var newGoal : nextGoals) {
                boolean closedGoal = newGoal.node().isClosed();
                if (!closedGoal) {
                    openGoals.addFirst(newGoal);
                }
            }
        }

        return saveProof(originalProof, proof);
    }

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
            // TODO(slicing): leave goal open?
            return RuleAppSMT.rule.createApp(null, proof.getServices());
        }

        IBuiltInRuleApp ourApp = null;
        PosInOccurrence pos = null;

        if (stepIdxToPos.get(originalStep.getStepIndex()) != null) { // otherwise we have no pos
            PosInOccurrence oldPos = stepIdxToPos.get(originalStep.getStepIndex());
            pos = findInNewSequent(oldPos, currGoal.sequent());
            if (pos == null) {
                LOGGER.error("failed to find new formula @ built-in rule name {}, serial nr {}",
                    ruleName, originalStep.getStepIndex());
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

            currContract = null;
            if (builtinIfInsts != null) {
                ourApp = ourApp.setIfInsts(builtinIfInsts);
                builtinIfInsts = null;
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
            ourApp.setIfInsts(builtinIfInsts);
            ((OneStepSimplifierRuleApp) ourApp).restrictedIfInsts = true;
        }
        builtinIfInsts = null;
        return ourApp;
    }

    private TacletApp constructTacletApp(Node originalStep, Goal currGoal)
            throws TacletAppConstructionException {

        final String tacletName = originalStep.getAppliedRuleApp().rule().name().toString();

        TacletApp ourApp = null;
        PosInOccurrence pos = null;

        Taclet t = proof.getInitConfig()
                .lookupActiveTaclet(new Name(tacletName));
        if (t == null) {
            if (stepIndexToDynamicRule.containsKey(originalStep.getStepIndex())) {
                var idx = stepIndexToDynamicRule.get(originalStep.getStepIndex());
                // find the correct taclet
                boolean done = false;
                for (var partialApp : currGoal.indexOfTaclets().getPartialInstantiatedApps()) {
                    if (Objects.equals(newStepsToStepIndices.get(partialApp.taclet().getAddedBy()),
                        idx)) {
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
        Services services = proof.getServices();

        var oldPos = originalStep.getAppliedRuleApp().posInOccurrence();
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

        var app = originalStep.getAppliedRuleApp();
        assert app instanceof TacletApp;
        var tacletApp = (TacletApp) app;
        var instantantions = tacletApp.instantiations();
        ourApp = constructInsts(ourApp, currGoal,
            originalProofSaver.getInterestingInstantiations(instantantions), services);

        ImmutableList<IfFormulaInstantiation> ifFormulaList = ImmutableSLList.nil();
        var oldFormulas = stepIdxToIfInsts.get(originalStep.getStepIndex()).stream()
                .map(x -> new Pair<>(x, true))
                .collect(Collectors.toList());
        if (tacletApp instanceof PosTacletApp) {
            var posTacletApp = (PosTacletApp) tacletApp;
            if (posTacletApp.ifFormulaInstantiations() != null) {
                for (var x : posTacletApp.ifFormulaInstantiations()) {
                    if (x instanceof IfFormulaInstDirect) {
                        oldFormulas.add(new Pair<>(new PosInOccurrence(x.getConstrainedFormula(),
                            PosInTerm.getTopLevel(), true), false));
                    }
                }
            }
        }
        for (var oldFormulaPioSpec : oldFormulas) {
            var oldFormulaPio = oldFormulaPioSpec.first;
            var newPio = findInNewSequent(oldFormulaPio, currGoal.sequent());
            if (newPio == null) {
                throw new IllegalStateException(String.format(
                    "did not locate ifInst during slicing @ rule name %s, serial nr %d (orig. proof)",
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
