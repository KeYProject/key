/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.replay;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
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
import de.uka.ilkd.key.rule.RuleAppUtil;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.smt.SMTRuleApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.proof.io.OutputStreamProofSaver.printAnything;

/**
 * Abstract proof replayer/constructor. Always works based on a previous/original proof
 * and a "new" proof.
 *
 * @author Arne Keller
 */
public abstract class AbstractProofReplayer {
    /**
     * The original proof used when constructing the new proof.
     */
    private final Proof originalProof;
    /**
     * The new proof.
     */
    private final Proof proof;

    /**
     * Instantiate a new replayer.
     *
     * @param originalProof previous proof
     * @param proof new proof
     */
    protected AbstractProofReplayer(Proof originalProof, Proof proof) {
        this.originalProof = originalProof;
        this.proof = proof;
    }

    /**
     * Re-apply the provided node of the original proof on the goal in the new proof.
     *
     * @param node original proof node to re-apply
     * @param openGoal open goal to apply the proof node on
     * @return the new goals added by this rule application
     * @throws IntermediateProofReplayer.BuiltInConstructionException on error
     */
    protected ImmutableList<Goal> reApplyRuleApp(Node node, Goal openGoal)
            throws IntermediateProofReplayer.BuiltInConstructionException {
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
                "don't know how to copy ruleapp " + ruleApp.rule().displayName());
        }
        return nextGoals;
    }

    /**
     * Construct a built-in based on the step in the original proof.
     *
     * @param originalStep step in original proof
     * @param currGoal open goal in proof slice
     * @return built-in rule app
     * @throws IntermediateProofReplayer.BuiltInConstructionException on error
     */
    private IBuiltInRuleApp constructBuiltinApp(Node originalStep, Goal currGoal)
            throws IntermediateProofReplayer.BuiltInConstructionException {
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
        for (PosInOccurrence oldFormulaPio : RuleAppUtil
                .ifInstsOfRuleApp(originalStep.getAppliedRuleApp(), originalStep)) {
            PosInOccurrence newFormula = findInNewSequent(oldFormulaPio, currGoal.sequent());
            if (newFormula == null) {
                throw new IllegalStateException(String.format(
                    "did not locate built-in ifInst during slicing @ rule name %s, serial nr %d",
                    ruleName, originalStep.serialNr()));
            }
            builtinIfInsts = builtinIfInsts.append(newFormula);
        }

        if (SMTRuleApp.RULE.displayName().equals(ruleName)) {
            return SMTRuleApp.RULE.createApp(null, proof.getServices());
        }

        IBuiltInRuleApp ourApp = null;
        PosInOccurrence pos = null;

        if (originalStep.getAppliedRuleApp().posInOccurrence() != null) { // otherwise we have no
                                                                          // pos
            PosInOccurrence oldPos = originalStep.getAppliedRuleApp().posInOccurrence();
            pos = findInNewSequent(oldPos, currGoal.sequent());
            if (pos == null) {
                throw new IllegalStateException("failed to find new formula");
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
                // copy over the mysterious "step"
                PosInOccurrence step = findInNewSequent(((UseDependencyContractApp) ruleApp).step(),
                    currGoal.sequent());
                contractApp = (((UseDependencyContractRule) useContractRule)
                        .createApp(pos)).setContract(currContract).setStep(step);
            }

            if (contractApp.check(currGoal.proof().getServices()) == null) {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    "Cannot apply contract: " + currContract);
            } else {
                ourApp = contractApp;
            }

            if (builtinIfInsts != null) {
                ourApp = ourApp.setIfInsts(builtinIfInsts);
            }
            return ourApp;
        }

        final ImmutableSet<IBuiltInRuleApp> ruleApps = IntermediateProofReplayer.collectAppsForRule(
            ruleName, currGoal, pos);
        if (ruleApps.size() != 1) {
            if (ruleApps.size() < 1) {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    ruleName + " is missing. Most probably the binary "
                        + "for this built-in rule is not in your path or "
                        + "you do not have the permission to execute it.");
            } else {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
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
        TacletApp originalTacletApp = null;
        if (originalStep.getAppliedRuleApp() instanceof TacletApp) {
            originalTacletApp = (TacletApp) originalStep.getAppliedRuleApp();
        }

        TacletApp ourApp = null;
        PosInOccurrence pos = null;

        Taclet t = proof.getInitConfig()
                .lookupActiveTaclet(new Name(tacletName));
        if (t == null) {
            // find the correct taclet
            for (NoPosTacletApp partialApp : currGoal.indexOfTaclets()
                    .getPartialInstantiatedApps()) {
                if (partialApp.equalsModProofIrrelevancy(originalTacletApp)) {
                    ourApp = partialApp;
                    break;
                }
            }
            if (ourApp == null) {
                ourApp = currGoal.indexOfTaclets().lookup(tacletName);
            }
            if (ourApp == null) {
                throw new IllegalStateException(
                    "proof replayer failed to find dynamically added taclet");
            }
        } else {
            ourApp = NoPosTacletApp.createNoPosTacletApp(t);
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
        ourApp = IntermediateProofReplayer.constructInsts(ourApp, currGoal,
            getInterestingInstantiations(instantantions), services);

        ImmutableList<IfFormulaInstantiation> ifFormulaList = ImmutableSLList.nil();
        List<Pair<PosInOccurrence, Boolean>> oldFormulas = RuleAppUtil
                .ifInstsOfRuleApp(originalStep.getAppliedRuleApp(), originalStep)
                .stream()
                .map(x -> new Pair<>(x, true))
                .collect(Collectors.toList());
        // add direct instantiations
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

    /**
     * Get the "interesting" instantiations of the provided object.
     *
     * @param inst instantiations
     * @return the "interesting" instantiations (serialized)
     */
    public Collection<String> getInterestingInstantiations(SVInstantiations inst) {
        Collection<String> s = new ArrayList<>();

        for (final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> pair : inst
                .interesting()) {
            final SchemaVariable var = pair.key();

            final Object value = pair.value().getInstantiation();

            if (!(value instanceof Term || value instanceof ProgramElement
                    || value instanceof Name)) {
                throw new IllegalStateException("Saving failed.\n"
                    + "FIXME: Unhandled instantiation type: " + value.getClass());
            }

            String singleInstantiation =
                var.name() + "=" + printAnything(value, proof.getServices(), false);
            s.add(singleInstantiation);
        }

        return s;
    }
}
