/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletPrefixBuilder;

import org.key_project.logic.Name;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Builds the rule which inserts information flow contract applications.
 *
 * @author christoph
 */
abstract class AbstractInfFlowContractAppTacletBuilder extends AbstractInfFlowTacletBuilder {

    private JTerm[] contextUpdates;
    private ProofObligationVars poVars;
    static final String USE_IF = InfFlowContractAppTaclet.USE_IF;
    private static final String IF_CONTRACT_APPLICATION = "information_flow_contract_appl";

    protected AbstractInfFlowContractAppTacletBuilder(final Services services) {
        super(services);
    }

    public void setContextUpdate(JTerm... contextUpdates) {
        this.contextUpdates = contextUpdates;
    }

    public void setProofObligationVars(ProofObligationVars poVars) {
        this.poVars = poVars;
    }

    public JTerm buildContractApplPredTerm() {
        ProofObligationVars appData = poVars;
        JTerm contractApplPredTerm = getContractApplPred(appData);
        for (JTerm update : contextUpdates) {
            contractApplPredTerm = apply(update, contractApplPredTerm);
        }
        return contractApplPredTerm;
    }

    /**
     * Builds the taclet.
     *
     * @param goal the goal
     * @return the taclet
     */
    public Taclet buildTaclet(Goal goal) {
        ProofObligationVars appData = poVars;
        return genInfFlowContractApplTaclet(goal, appData, services);
    }

    abstract Name generateName();

    private static Name makeUnique(Name name, Goal goal) {
        int i = 0;
        final String s = name.toString();
        name = new Name(s + "_" + getBranchUID(goal.node()));
        while (InfFlowContractAppTaclet.registered(name)) {
            name = new Name(s + "_" + i++);
        }
        InfFlowContractAppTaclet.register(name);
        return name;
    }

    /**
     * Returns a string which uniquely identifies the smallest branch of the proof tree containing
     * the specified node, i.e., a string which encodes branching on the path from the root to the
     * specified node.
     *
     * @param node a node.
     * @return a string which uniquely identifies the smallest branch of the proof tree containing
     *         the specified node.
     */
    private static String getBranchUID(Node node) {
        final int base = Character.MAX_RADIX;
        StringBuilder path = new StringBuilder();
        int zeroCount = 0;

        while (!node.root() && node.parent().childrenCount() <= 1) {
            node = node.parent();
        }

        // For each branching in the path, append the number of the branch in base-36
        // (using 0-9 and a-z as digits) followed by a '_'.
        // Then shorten the string by replacing successive '_'s. E.g., replace "___" by "_3_".
        while (!node.root()) {
            for (int i = node.siblingNr(); i > 0; i /= base) {
                zeroCount = 0;
                path.append("_");
                path.append(Integer.toString(zeroCount, Character.MAX_RADIX));
                path.append("_");

                path.append(i % base);
            }

            zeroCount++;
            node = node.parent();

            while (!node.root() && node.parent().childrenCount() <= 1) {
                node = node.parent();
            }
        }

        path.append("_");
        path.append(Integer.toString(zeroCount, Character.MAX_RADIX));
        path.append("_");

        return path.toString();
    }

    /**
     * Generate schema assumes term.
     *
     * @param schemaDataAssumes the proof obligation variables for the schema data assumes
     * @param services the services
     * @return the term
     */
    abstract JTerm generateSchemaAssumes(ProofObligationVars schemaDataAssumes, Services services);

    /**
     * Generate schema find term.
     *
     * @param schemaDataFind the proof obligation variables for the schema data find
     * @param services the services
     * @return the term
     */
    abstract JTerm generateSchemaFind(ProofObligationVars schemaDataFind, Services services);

    /**
     * Gets the contract application predicate.
     *
     * @param appData the proof obligation variables for the application data
     * @return the contract application predicate
     */
    abstract JTerm getContractApplPred(ProofObligationVars appData);

    /**
     * Generate application data schema variables.
     *
     * @param schemaPrefix the schema prefix
     * @param appData the proof obligation variables for the application data
     * @param services the services object
     * @return the proof obligation variables
     */
    ProofObligationVars generateApplicationDataSVs(String schemaPrefix, ProofObligationVars appData,
            Services services) {
        // generate a new schema variable for any pre variable
        JTerm selfAtPreSV = createTermSV(appData.pre.self, schemaPrefix, services);
        ImmutableList<JTerm> localVarsAtPreSVs =
            createTermSV(appData.pre.localVars, schemaPrefix, services);
        JTerm guardAtPreSV = createTermSV(appData.pre.guard, schemaPrefix, services);
        JTerm resAtPreSV = createTermSV(appData.pre.result, schemaPrefix, services);
        JTerm excAtPreSV = createTermSV(appData.pre.exception, schemaPrefix, services);
        JTerm heapAtPreSV = createTermSV(appData.pre.heap, schemaPrefix, services);
        JTerm mbyAtPreSV = createTermSV(appData.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        JTerm selfAtPostSV = (appData.pre.self == appData.post.self ? selfAtPreSV
                : createTermSV(appData.post.self, schemaPrefix, services));

        ImmutableList<JTerm> localVarsAtPostSVs = ImmutableSLList.nil();
        Iterator<JTerm> appDataPreLocalVarsIt = appData.pre.localVars.iterator();
        Iterator<JTerm> schemaLocalVarsAtPreIt = localVarsAtPreSVs.iterator();
        for (JTerm appDataPostLocalVar : appData.post.localVars) {
            JTerm appDataPreLocalVar = appDataPreLocalVarsIt.next();
            JTerm localPreVar = schemaLocalVarsAtPreIt.next();
            if (appDataPostLocalVar == appDataPreLocalVar) {
                localVarsAtPostSVs = localVarsAtPostSVs.append(localPreVar);
            } else {
                localVarsAtPostSVs = localVarsAtPostSVs
                        .append(createTermSV(appDataPostLocalVar, schemaPrefix, services));
            }
        }

        JTerm guardAtPostSV = (appData.pre.guard == appData.post.guard ? guardAtPreSV
                : createTermSV(appData.post.guard, schemaPrefix, services));
        JTerm resAtPostSV = (appData.pre.result == appData.post.result ? resAtPreSV
                : createTermSV(appData.post.result, schemaPrefix, services));
        JTerm excAtPostSV = (appData.pre.exception == appData.post.exception ? excAtPreSV
                : createTermSV(appData.post.exception, schemaPrefix, services));
        JTerm heapAtPostSV = (appData.pre.heap == appData.post.heap ? heapAtPreSV
                : createTermSV(appData.post.heap, schemaPrefix, services));

        // build state vararibale container for pre and post state
        StateVars pre = new StateVars(selfAtPreSV, guardAtPreSV, localVarsAtPreSVs, resAtPreSV,
            excAtPreSV, heapAtPreSV, mbyAtPreSV);
        StateVars post = new StateVars(selfAtPostSV, guardAtPostSV, localVarsAtPostSVs, resAtPostSV,
            excAtPostSV, heapAtPostSV, null);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post, poVars.exceptionParameter, poVars.formalParams,
            services);
    }

    private Taclet genInfFlowContractApplTaclet(Goal goal, ProofObligationVars appData,
            Services services) {
        Name tacletName = makeUnique(generateName(), goal);
        // generate schemaFind and schemaAssumes terms
        ProofObligationVars schemaDataFind = generateApplicationDataSVs("find_", appData, services);
        JTerm schemaFind = generateSchemaFind(schemaDataFind, services);
        ProofObligationVars schemaDataAssumes =
            generateApplicationDataSVs("assumes_", appData, services);
        JTerm schemaAssumes = generateSchemaAssumes(schemaDataAssumes, services);

        // generate post term
        JTerm replaceWithTerm =
            buildContractApplications(schemaDataFind, schemaDataAssumes, services);

        // collect quantifiable variables of the post term and replace them
        // by schema variables
        Map<QuantifiableVariable, VariableSV> quantifiableVarsToSchemaVars =
            collectQuantifiableVariables(schemaFind, services);
        quantifiableVarsToSchemaVars.putAll(collectQuantifiableVariables(schemaAssumes, services));
        quantifiableVarsToSchemaVars
                .putAll(collectQuantifiableVariables(replaceWithTerm, services));
        final OpReplacer or = new OpReplacer(quantifiableVarsToSchemaVars,
            services.getTermFactory(), services.getProof());
        schemaFind = or.replace(schemaFind);
        schemaAssumes = or.replace(schemaAssumes);
        replaceWithTerm = or.replace(replaceWithTerm);

        // create sequents
        Sequent assumesSeq =
            JavaDLSequentKit.createAnteSequent(
                ImmutableSLList.singleton(new SequentFormula(schemaAssumes)));
        Sequent replaceWithSeq =
            JavaDLSequentKit.createAnteSequent(
                ImmutableSLList.singleton(new SequentFormula(replaceWithTerm)));

        // create taclet
        InfFlowContractAppRewriteTacletBuilder tacletBuilder =
            new InfFlowContractAppRewriteTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind);
        tacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.ANTECEDENT_POLARITY));
        tacletBuilder.setIfSequent(assumesSeq);
        RewriteTacletGoalTemplate goalTemplate = new RewriteTacletGoalTemplate(replaceWithSeq,
            ImmutableSLList.nil(), schemaFind);
        tacletBuilder.addTacletGoalTemplate(goalTemplate);
        tacletBuilder.addRuleSet(new RuleSet(new Name(IF_CONTRACT_APPLICATION)));
        tacletBuilder.setSurviveSmbExec(true);
        addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values());
        return tacletBuilder.getTaclet();
    }

    abstract JTerm buildContractApplications(ProofObligationVars contAppData,
            ProofObligationVars contAppData2, Services services);

    /**
     * A normal RewriteTacletBuilder except that an InfFlowContractAppTaclet is returned instead of
     * a normal RewriteTaclet. InfFlowContractAppTaclet's are normal RewriteTaclet's except that the
     * formula which is added by the taclets are also added to the list of formulas contained in the
     * INF_FLOW_CONTRACT_APPL_PROPERTY. The INF_FLOW_CONTRACT_APPL_PROPERTY is used by the macros
     * UseInformationFlowContractMacro and PrepareInfFlowContractPreBranchesMacro to decide how to
     * prepare the formulas resulting from information flow contract applications.
     */
    private static class InfFlowContractAppRewriteTacletBuilder
            extends RewriteTacletBuilder<InfFlowContractAppTaclet> {

        InfFlowContractAppRewriteTacletBuilder() {
        }

        @Override
        public InfFlowContractAppTaclet getRewriteTaclet() {
            if (find == null) {
                throw new TacletBuilder.TacletBuilderException(this, "No find part specified");

            }
            checkBoundInIfAndFind();
            TacletPrefixBuilder prefixBuilder = new TacletPrefixBuilder(this);
            prefixBuilder.build();
            return new InfFlowContractAppTaclet(name,
                new TacletApplPart(ifseq, applicationRestriction, varsNew, varsNotFreeIn,
                    varsNewDependingOn,
                    variableConditions),
                goals, ruleSets, attrs, (JTerm) find, prefixBuilder.getPrefixMap(),
                choices, surviveSmbExec, tacletAnnotations);

        }
    }
}
