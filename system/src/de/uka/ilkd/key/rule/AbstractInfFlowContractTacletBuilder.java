// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.tacletbuilder.InfFlowTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
abstract class AbstractInfFlowContractTacletBuilder extends TermBuilder.Serviced {

    private Term contextUpdate;
    private Term contractSelf;
    private ImmutableList<Term> localIns;
    private Term heapAtPre;
    private ImmutableList<Term> localOuts;
    private Term contractResult;
    private Term exceptionVar;
    private Term heapAtPost;


    public AbstractInfFlowContractTacletBuilder(final Services services) {
        super(services);
        this.localIns = ImmutableSLList.<Term>nil();
        this.localOuts = ImmutableSLList.<Term>nil();
    }


    public void setContextUpdate(Term contextUpdate) {
        this.contextUpdate = contextUpdate;
    }


    public void setHeapAtPre(Term heapAtPre) {
        this.heapAtPre = heapAtPre;
    }


    public void setHeapAtPost(Term heapAtPost) {
        this.heapAtPost = heapAtPost;
    }


    public void setSelf(Term contractSelf) {
        this.contractSelf = contractSelf;
    }


    public void setLocalIns(ImmutableList<Term> localIns) {
        this.localIns = localIns;
    }


    public void setLocalOuts(ImmutableList<Term> localOuts) {
        this.localOuts = localOuts;
    }


    public void setResult(Term contractResult) {
        this.contractResult = contractResult;
    }


    public void setException(Term exceptionVar) {
        this.exceptionVar = exceptionVar;
    }


    // TODO: add exception var
    public Term buildContractApplPredTerm() {
        ProofObligationVars appData = getProofObligationVars();
        final Term contractApplPredTerm = getContractApplPred(appData);
        return apply(contextUpdate, contractApplPredTerm);
    }


    // TODO: add exception var
    public Taclet buildContractApplTaclet() {
        ProofObligationVars appData = getProofObligationVars();
        return genInfFlowContractApplTaclet(appData, services);
    }


    abstract Name generateName();


    abstract Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                                        Services services);


    abstract Term generateSchemaFind(ProofObligationVars schemaDataFind,
                                     Services services);


    private ProofObligationVars getProofObligationVars() {
        return new ProofObligationVars(contractSelf, localIns,
                                       heapAtPre, localOuts, contractResult,
                                       exceptionVar, heapAtPost, services);
    }


    abstract Term getContractApplPred(ProofObligationVars appData);


    private ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
                                                           ProofObligationVars appData,
                                                           Services services) {
        Term selfSV = createTermSV(appData.self, schemaPrefix, services);
        Term selfAtPostSV =
                createTermSV(appData.selfAtPost, schemaPrefix, services);
        ImmutableList<Term> localInSVs =
                createTermSV(appData.localIns, schemaPrefix, services);
        ImmutableList<Term> localOutSVs =
                createTermSV(appData.localOuts, schemaPrefix, services);
        Term resSV = createTermSV(appData.result, schemaPrefix, services);
        Term resAtPostSV =
                createTermSV(appData.resultAtPost, schemaPrefix, services);
        Term excSV = createTermSV(appData.exception, schemaPrefix, services);
        Term excAtPostSV =
                createTermSV(appData.exceptionAtPost, schemaPrefix, services);
        Term heapSV = createTermSV(appData.heap, schemaPrefix, services);
        Term heapAtPreSV =
                createTermSV(appData.heapAtPre, schemaPrefix, services);
        Term heapAtPostSV =
                createTermSV(appData.heapAtPost, schemaPrefix, services);
        Term mbyAtPreSV =
                createTermSV(appData.mbyAtPre, schemaPrefix, services);

        return new ProofObligationVars(selfSV, selfAtPostSV, localInSVs,
                                       localOutSVs, resSV, resAtPostSV, excSV,
                                       excAtPostSV, heapSV, heapAtPreSV,
                                       heapAtPostSV, mbyAtPreSV, "", services);
    }


    private Taclet genInfFlowContractApplTaclet(ProofObligationVars appData,
                                                Services services) {
        Name tacletName = generateName();

        // genreate schemaFind and schemaAssumes terms
        ProofObligationVars schemaDataFind = generateApplicationDataSVs(
                "find_", appData, services);
        Term schemaFind = generateSchemaFind(schemaDataFind, services);
        ProofObligationVars schemaDataAssumes = generateApplicationDataSVs(
                "assumes_", appData, services);
        Term schemaAssumes = generateSchemaAssumes(schemaDataAssumes, services);

        // generate post term
        Term schemaContApps =
                buildContractApplications(schemaDataFind,
                                          schemaDataAssumes, services);

        //create sequents
        Sequent assumesSeq = Sequent.createAnteSequent(
                new Semisequent(new SequentFormula(schemaAssumes)));
        Sequent axiomSeq = Sequent.createAnteSequent(
                new Semisequent(new SequentFormula(schemaContApps)));

        //create taclet
        InfFlowTacletBuilder tacletBuilder = new InfFlowTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.ANTECEDENT_POLARITY);
        tacletBuilder.setIfSequent(assumesSeq);
        RewriteTacletGoalTemplate goalTemplate =
                new RewriteTacletGoalTemplate(axiomSeq,
                                              ImmutableSLList.<Taclet>nil(),
                                              schemaFind);
        tacletBuilder.addTacletGoalTemplate(goalTemplate);
        tacletBuilder.addRuleSet(new RuleSet(new Name("information_flow_contract_appl")));
        tacletBuilder.setSurviveSmbExec(true);
        return tacletBuilder.getTaclet();
    }


    private ImmutableList<Term> createTermSV(ImmutableList<Term> ts,
                                             String schemaPrefix,
                                             Services services) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term t : ts) {
            result = result.append(createTermSV(t, schemaPrefix, services));
        }
        return result;
    }


    private Term createTermSV(Term t,
                              String schemaPrefix,
                              Services services) {
        if (t == null) {
            return null;
        }
        String svName = schemaPrefix + t.toString();
        Sort sort = t.sort();
        Name name =
                services.getVariableNamer().getTemporaryNameProposal(svName);
        return var(SchemaVariableFactory.createTermSV(name, sort));

    }


    abstract Term buildContractApplications(ProofObligationVars contAppData,
                                            ProofObligationVars contAppData2,
                                            Services services);
}
