/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowBlockContractTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * <p>
 * Rule for the application of {@link BlockContract}s.
 * </p>
 *
 * @see AbstractBlockContractBuiltInRuleApp
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractBlockContractRule extends AbstractAuxiliaryContractRule {

    /**
     *
     * @param instantiation an instantiation.
     * @param goal the current goal.
     * @param services services.
     * @return all applicable block contracts for the instantiation.
     */
    public static ImmutableSet<BlockContract> getApplicableContracts(
            final Instantiation instantiation, final Goal goal, final Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.nil();
        }
        return getApplicableContracts(services.getSpecificationRepository(),
            instantiation.statement(), instantiation.modality().kind(), goal);
    }

    /**
     * @param specifications a specification repository.
     * @param statement a block.
     * @param modalityKind the current goal's modality.
     * @param goal the current goal.
     * @return all applicable block contracts for the block from the repository.
     */
    public static ImmutableSet<BlockContract> getApplicableContracts(
            final SpecificationRepository specifications, final JavaStatement statement,
            final JModality.JavaModalityKind modalityKind, final Goal goal) {
        if (statement instanceof StatementBlock block) {

            ImmutableSet<BlockContract> collectedContracts =
                specifications.getBlockContracts(block, modalityKind);
            if (modalityKind == JModality.JavaModalityKind.BOX) {
                collectedContracts =
                    collectedContracts.union(
                        specifications.getBlockContracts(block, JModality.JavaModalityKind.DIA));
            } else if (modalityKind == JModality.JavaModalityKind.BOX_TRANSACTION) {
                collectedContracts = collectedContracts
                        .union(specifications.getBlockContracts(block,
                            JModality.JavaModalityKind.DIA_TRANSACTION));
            }
            return filterAppliedContracts(collectedContracts, goal);
        } else {
            return null;
        }
    }

    /**
     *
     * @param collectedContracts a set of block contracts.
     * @param goal the current goal.
     * @return the set with all non-applicable contracts filtered out.
     */
    protected static ImmutableSet<BlockContract> filterAppliedContracts(
            final ImmutableSet<BlockContract> collectedContracts, final Goal goal) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        for (BlockContract contract : collectedContracts) {
            if (!contractApplied(contract, goal) || InfFlowCheckInfo.isInfFlow(goal)) {
                result = result.add(contract);
            }
        }
        return result;
    }

    /**
     *
     * @param contract a block contract.
     * @param goal the current goal.
     * @return {@code true} if the contract has already been applied.
     */
    protected static boolean contractApplied(final BlockContract contract, final Goal goal) {
        Node selfOrParentNode = goal.node();
        Node previousNode = null;
        while (selfOrParentNode != null) {
            RuleApp app = selfOrParentNode.getAppliedRuleApp();
            if (app instanceof BlockContractInternalBuiltInRuleApp blockRuleApp) {
                if (blockRuleApp.getStatement().equals(contract.getBlock())
                        && selfOrParentNode.getChildNr(previousNode) == 0) {
                    // prevent application of contract in its own check validity branch
                    // but not in other branches, e.g., do-while
                    // loops might need to apply the same contract
                    // twice in its usage branch
                    return true;
                }
            }
            previousNode = selfOrParentNode;
            selfOrParentNode = selfOrParentNode.parent();
        }

        Services services = goal.proof().getServices();
        Proof proof = goal.proof();
        ProofOblInput po = services.getSpecificationRepository().getProofOblInput(proof);

        if (po instanceof FunctionalBlockContractPO
                && contract.getBlock().equals(((FunctionalBlockContractPO) po).getBlock())) {
            return true;
        }

        if (po instanceof SymbolicExecutionPO) {
            Goal initiatingGoal = ((SymbolicExecutionPO) po).getInitiatingGoal();
            return contractApplied(contract, initiatingGoal);
        } else if (po instanceof BlockExecutionPO) {
            Goal initiatingGoal = ((BlockExecutionPO) po).getInitiatingGoal();
            return contractApplied(contract, initiatingGoal);
        } else {
            return false;
        }
    }

    /**
     *
     * @param variables variables.
     * @param contract a block contract.
     * @param services services.
     * @return a map from every variable that is changed in the block to its anonymization constant.
     */
    protected static Map<LocationVariable, Function> createAndRegisterAnonymisationVariables(
            final Iterable<LocationVariable> variables, final BlockContract contract,
            final TermServices services) {
        Map<LocationVariable, Function> result = new LinkedHashMap<>(40);
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable variable : variables) {
            if (contract.hasModifiableClause(variable)) {
                final String anonymisationName =
                    tb.newName(AuxiliaryContractBuilders.ANON_OUT_PREFIX + variable.name());
                final Function anonymisationFunction =
                    new JFunction(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                result.put(variable, anonymisationFunction);
            }
        }
        return result;
    }

    /*
     * Factory methods for information flow contracts.
     *
     * TODO These could be moved into a separate class (like BlockContractBuilders) to allow them to
     * be reused in other classes.
     */

    protected static JTerm buildAfterVar(JTerm varTerm, String suffix, Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = "_" + suffix;
        }
        String name = tb.newName(varTerm + "_After" + suffix);
        LocationVariable varAtPostVar =
            new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        JTerm varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }

    protected static ImmutableList<JTerm> buildLocalOutsAtPre(ImmutableList<JTerm> varTerms,
            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> renamedLocalOuts = ImmutableSLList.nil();
        for (JTerm varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();

            String name = tb.newName(varTerm + "_Before");
            LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            JTerm varAtPost = tb.var(varAtPostVar);
            renamedLocalOuts = renamedLocalOuts.append(varAtPost);
        }
        return renamedLocalOuts;
    }

    protected static ImmutableList<JTerm> buildLocalOutsAtPost(ImmutableList<JTerm> varTerms,
            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> renamedLocalOuts = ImmutableSLList.nil();
        for (JTerm varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();

            String name = tb.newName(varTerm + "_After");
            LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            JTerm varAtPost = tb.var(varAtPostVar);
            renamedLocalOuts = renamedLocalOuts.append(varAtPost);
        }
        return renamedLocalOuts;
    }

    protected static JTerm buildInfFlowPreAssumption(ProofObligationVars instVars,
            ImmutableList<JTerm> localOuts, ImmutableList<JTerm> localOutsAtPre, JTerm baseHeap,
            final TermBuilder tb) {
        JTerm beforeAssumptions = tb.equals(instVars.pre.heap, baseHeap);
        Iterator<JTerm> outsAtPre = localOutsAtPre.iterator();
        for (JTerm locOut : localOuts) {
            beforeAssumptions = tb.and(beforeAssumptions, tb.equals(outsAtPre.next(), locOut));
        }
        return beforeAssumptions;
    }

    protected static JTerm buildInfFlowPostAssumption(ProofObligationVars instVars,
            ImmutableList<JTerm> localOuts, ImmutableList<JTerm> localOutsAtPost, JTerm baseHeap,
            JTerm applPredTerm, final TermBuilder tb) {
        JTerm resultEq =
            instVars.pre.result != null ? tb.equals(instVars.post.result, instVars.pre.result)
                    : tb.tt();
        JTerm exceptionEq = instVars.pre.exception != null
                ? tb.equals(instVars.post.exception, instVars.pre.exception)
                : tb.tt();
        JTerm selfEq =
            instVars.pre.self != null ? tb.equals(instVars.post.self, instVars.pre.self) : tb.tt();
        JTerm afterAssumptions =
            tb.and(tb.equals(instVars.post.heap, baseHeap), selfEq, resultEq, exceptionEq);
        Iterator<JTerm> outAtPost = localOutsAtPost.iterator();
        for (JTerm locOut : localOuts) {
            afterAssumptions = tb.and(afterAssumptions, tb.equals(outAtPost.next(), locOut));
        }
        afterAssumptions = tb.and(afterAssumptions, applPredTerm);

        return afterAssumptions;
    }

    static SequentFormula buildBodyPreservesSequent(
            InfFlowPOSnippetFactory f, InfFlowProof proof) {
        JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);
        JTerm post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        final TermBuilder tb = proof.getServices().getTermBuilder();

        final JTerm finalTerm =
            tb.imp(tb.label(selfComposedExec, ParameterlessTermLabel.SELF_COMPOSITION_LABEL), post);
        proof.addLabeledIFSymbol(selfComposedExec);

        return new SequentFormula(finalTerm);
    }

    private static ProofObligationVars generateProofObligationVariables(
            final AuxiliaryContract.Variables variables, final ProgramVariable exceptionParameter,
            final LocationVariable baseHeap, final ImmutableList<JTerm> localVarsAtPre,
            final ImmutableList<JTerm> localVarsAtPost, final Services services,
            final TermBuilder tb) {
        final boolean hasSelf = variables.self != null;
        final boolean hasRes = variables.result != null;
        final boolean hasExc = variables.exception != null;

        final JTerm heapAtPre = tb.var(variables.remembranceHeaps.get(baseHeap));
        final Name heapAtPostName = new Name(tb.newName("heap_After_BLOCK"));
        final JTerm heapAtPost = tb.func(new JFunction(heapAtPostName, heapAtPre.sort(), true));
        final JTerm selfAtPre = hasSelf ? tb.var(variables.self) : tb.NULL();
        final JTerm selfAtPost = hasSelf ? buildAfterVar(selfAtPre, "BLOCK", services) : tb.NULL();

        JTerm resultAtPre = hasRes ? tb.var(variables.result) : tb.NULL();
        final JTerm resultAtPost =
            hasRes ? buildAfterVar(resultAtPre, "BLOCK", services) : tb.NULL();
        final JTerm exceptionAtPre = hasExc ? tb.var(variables.exception) : tb.NULL();
        final JTerm exceptionAtPost =
            hasExc ? buildAfterVar(exceptionAtPre, "BLOCK", services) : tb.NULL();

        // generate proof obligation variables
        final StateVars instantiationPreVars = new StateVars(hasSelf ? selfAtPre : null,
            localVarsAtPre, hasRes ? resultAtPre : null, hasExc ? exceptionAtPre : null, heapAtPre);
        final StateVars instantiationPostVars =
            new StateVars(hasSelf ? selfAtPost : null, localVarsAtPost,
                hasRes ? resultAtPost : null, hasExc ? exceptionAtPost : null, heapAtPost);
        final ProofObligationVars instantiationVars = new ProofObligationVars(instantiationPreVars,
            instantiationPostVars, tb.var(exceptionParameter), null, tb);
        return instantiationVars;
    }

    private static void addProofObligation(final Goal infFlowGoal, final InfFlowProof proof,
            final BlockContract contract, final IFProofObligationVars ifVars,
            final ExecutionContext ec, final Services services) {
        // create proof obligation
        InfFlowPOSnippetFactory infFlowFactory =
            POSnippetFactory.getInfFlowFactory(contract, ifVars.c1, ifVars.c2, ec, services);

        final SequentFormula poFormula =
            buildBodyPreservesSequent(infFlowFactory, proof);

        // add proof obligation to goal
        infFlowGoal.addFormula(poFormula, false, true);
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        if (occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }
        final Instantiation instantiation =
            instantiate((JTerm) occurrence.subTerm(), goal);
        if (instantiation == null) {
            return false;
        }
        final ImmutableSet<BlockContract> contracts =
            getApplicableContracts(instantiation, goal, goal.proof().getServices());
        return !contracts.isEmpty();
    }

    /**
     * @param formula the formula on which the rule is to be applied.
     * @param goal the current goal.
     * @return a new instantiation.
     */
    public Instantiation instantiate(final JTerm formula, final Goal goal) {
        if (formula == getLastFocusTerm()) {
            return getLastInstantiation();
        } else {
            final Instantiation result = new Instantiator(formula, goal).instantiate();
            setLastFocusTerm(formula);
            setLastInstantiation(result);
            return result;
        }
    }

    protected void setUpInfFlowPartOfUsageGoal(final Goal usageGoal,
            InfFlowValidityData infFlowValitidyData, final JTerm contextUpdate,
            final JTerm remembranceUpdate, final JTerm anonymisationUpdate, final TermBuilder tb) {
        usageGoal.addTaclet(infFlowValitidyData.taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            true);
        final JTerm uAssumptions =
            tb.applySequential(new JTerm[] { contextUpdate, remembranceUpdate },
                tb.and(infFlowValitidyData.preAssumption,
                    tb.apply(anonymisationUpdate, infFlowValitidyData.postAssumption)));
        usageGoal.addFormula(new SequentFormula(uAssumptions), true, false);
    }

    protected InfFlowValidityData setUpInfFlowValidityGoal(final Goal infFlowGoal,
            final BlockContract contract,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final Services services, final AuxiliaryContract.Variables variables,
            final ProgramVariable exceptionParameter, final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ImmutableSet<LocationVariable> localOutVariables,
            final BlockContractInternalBuiltInRuleApp application,
            final Instantiation instantiation) {
        assert heaps.size() == 1 && anonymisationHeaps.size() <= 1
                : "information flow extension is at the moment not "
                    + "compatible with the non-base-heap setting";
        // prepare information flow analysis
        final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        final TermBuilder tb = services.getTermBuilder();
        assert infFlowGoal.proof() instanceof InfFlowProof;
        final InfFlowProof proof = (InfFlowProof) infFlowGoal.proof();

        final ImmutableList<JTerm> localIns = MiscTools.toTermList(localInVariables, tb);
        final ImmutableList<JTerm> localOuts = MiscTools.toTermList(localOutVariables, tb);
        final ImmutableList<JTerm> localOutsAtPre = buildLocalOutsAtPre(localOuts, services);
        final ImmutableList<JTerm> localOutsAtPost = buildLocalOutsAtPost(localOuts, services);
        final ImmutableList<JTerm> localInsWithoutOutDuplicates =
            MiscTools.filterOutDuplicates(localIns, localOuts);
        final ImmutableList<JTerm> localVarsAtPre =
            localInsWithoutOutDuplicates.append(localOutsAtPre);
        final ImmutableList<JTerm> localVarsAtPost =
            localInsWithoutOutDuplicates.append(localOutsAtPost);
        final ProofObligationVars instantiationVars = generateProofObligationVariables(variables,
            exceptionParameter, baseHeap, localVarsAtPre, localVarsAtPost, services, tb);
        final IFProofObligationVars ifVars = new IFProofObligationVars(instantiationVars, services);
        application.update(ifVars, instantiation.context());

        // generate information flow contract application predicate
        // and associated taclet
        final InfFlowBlockContractTacletBuilder ifContractBuilder =
            new InfFlowBlockContractTacletBuilder(services);
        ifContractBuilder.setContract(contract);
        ifContractBuilder.setExecutionContext(instantiation.context());
        ifContractBuilder.setContextUpdate(); // updates are handled by setUpUsageGoal
        ifContractBuilder.setProofObligationVars(instantiationVars);
        final JTerm contractApplTerm = ifContractBuilder.buildContractApplPredTerm();
        Taclet informationFlowContractApp = ifContractBuilder.buildTaclet(infFlowGoal);

        // get infFlowAssumptions
        final JTerm infFlowPreAssumption = buildInfFlowPreAssumption(instantiationVars, localOuts,
            localOutsAtPre, tb.var(baseHeap), tb);
        final JTerm infFlowPostAssumption = buildInfFlowPostAssumption(instantiationVars, localOuts,
            localOutsAtPost, tb.var(baseHeap), contractApplTerm, tb);
        addProofObligation(infFlowGoal, proof, contract, ifVars, instantiation.context(), services);

        proof.addIFSymbol(contractApplTerm);
        proof.addIFSymbol(informationFlowContractApp);
        proof.addGoalTemplates(informationFlowContractApp);
        return new InfFlowValidityData(infFlowPreAssumption, infFlowPostAssumption,
            informationFlowContractApp);
    }

    protected static class InfFlowValidityData {
        final JTerm preAssumption;
        final JTerm postAssumption;
        final Taclet taclet;

        public InfFlowValidityData(final JTerm preAssumption, final JTerm postAssumption,
                final Taclet taclet) {
            this.preAssumption = preAssumption;
            this.postAssumption = postAssumption;
            this.taclet = taclet;
        }
    }

    /**
     * A builder for {@link Instantiation}s.
     */
    protected static final class Instantiator extends AbstractAuxiliaryContractRule.Instantiator {

        /**
         *
         * @param formula the formula on which the rule is to be applied.
         * @param goal the current goal.
         */
        public Instantiator(final JTerm formula, final Goal goal) {
            super(formula, goal);
        }

        @Override
        protected boolean hasApplicableContracts(final Services services,
                final JavaStatement statement, final JModality.JavaModalityKind modalityKind,
                Goal goal) {
            ImmutableSet<BlockContract> contracts = getApplicableContracts(
                services.getSpecificationRepository(), statement, modalityKind, goal);

            return contracts != null && !contracts.isEmpty();
        }
    }

    public static class BlockContractHint {
        protected final static BlockContractHint USAGE_BRANCH =
            new BlockContractHint("Usage Branch");

        private final ProgramVariable excVar;

        private final String description;

        public BlockContractHint(String description) {
            this.description = description;
            this.excVar = null;
        }

        public BlockContractHint(String description, ProgramVariable excVar) {
            this.description = description;
            this.excVar = excVar;
        }

        public static BlockContractHint createUsageBranchHint() {
            return USAGE_BRANCH;
        }

        public static BlockContractHint createValidityBranchHint(ProgramVariable excVar) {
            return new BlockContractHint("Validity Branch", excVar);
        }

        public ProgramVariable getExceptionalVariable() {
            return excVar;
        }

        public String getDescription() {
            return description;
        }

        @Override
        public String toString() {
            return description
                    + (excVar != null ? "Validity Branch: exceptionVar=" + excVar.name() : "");
        }
    }
}
