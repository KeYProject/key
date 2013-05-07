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

    private Term[] contextUpdates;
    private Term contractSelf;
    private Term contractSelfAtPost;
    private ImmutableList<Term> localIns;
    private Term heapAtPre;
    private ImmutableList<Term> localOuts;
    private Term contractResult;
    private Term contractResultAtPost;
    private Term exceptionVar;
    private Term exceptionVarAtPost;
    private Term heapAtPost;
    private Term loopGuard;
    private Term loopGuardAtPost;


    public AbstractInfFlowContractTacletBuilder(final Services services) {
        super(services);
    }

    public void setContextUpdate(Term... contextUpdates) {
        this.contextUpdates = contextUpdates;
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
    
    public void setSelfAtPost(Term contractSelfAtPost) {
        this.contractSelfAtPost = contractSelfAtPost;
    }

    public void setGuard(Term guard) {
        this.loopGuard = guard;
    }

    public void setGuardAtPost(Term guardAtPost) {
        this.loopGuardAtPost = guardAtPost;
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

    public void setResultAtPost(Term resultAtPost) {
        this.contractResultAtPost = resultAtPost;
    }

    public void setException(Term exceptionVar) {
        this.exceptionVar = exceptionVar;
    }

    public void setExceptionAtPost(Term exceptionAtPost) {
        this.exceptionVarAtPost = exceptionAtPost;
    }

    // TODO: add exception var
    public Term buildContractApplPredTerm(boolean local) {
        ProofObligationVars appData = getProofObligationVars(local);
        Term contractApplPredTerm = getContractApplPred(appData);
        for (Term update : contextUpdates) {
            contractApplPredTerm = apply(update, contractApplPredTerm);
        }
        return contractApplPredTerm;
    }


    public Function getContractApplPred(boolean local) {
        ProofObligationVars appData = getProofObligationVars(local);
        Term contractApplPredTerm = getContractApplPred(appData);
        return contractApplPredTerm.op(Function.class);
    }


    // TODO: add exception var
    public Taclet buildContractApplTaclet(boolean local) {
        ProofObligationVars appData = getProofObligationVars(local);
        return genInfFlowContractApplTaclet(appData, services, local);
    }


    abstract Name generateName();


    abstract Term generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                                        Services services);


    abstract Term generateSchemaFind(ProofObligationVars schemaDataFind,
                                     Services services);


    private ProofObligationVars getProofObligationVars(boolean local) {
        return new ProofObligationVars(contractSelf, contractSelfAtPost, loopGuard, localIns,
                                       heapAtPre, loopGuardAtPost, localOuts, contractResult,
                                       contractResultAtPost, exceptionVar, exceptionVarAtPost,
                                       heapAtPost, services, local);
    }


    abstract Term getContractApplPred(ProofObligationVars appData);


    ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
                                                   ProofObligationVars appData,
                                                   Services services,
                                                   boolean local) {
        Term selfSV =
                createTermSV(appData.self, schemaPrefix, services);
        Term selfAtPostSV =
                createTermSV(appData.selfAtPost, schemaPrefix, services);
        ImmutableList<Term> localInSVs =
                createTermSV(appData.localIns, schemaPrefix, services);        
        Term guardSV =
                createTermSV(appData.guard, schemaPrefix, services);
        ImmutableList<Term> localOutSVs =
                createTermSV(appData.localOuts, schemaPrefix, services);
        Term guardAtPostSV =
                createTermSV(appData.guardAtPost, schemaPrefix, services);
        Term resSV =
                createTermSV(appData.result, schemaPrefix, services);
        Term resAtPostSV =
                createTermSV(appData.resultAtPost, schemaPrefix, services);
        Term excSV =
                createTermSV(appData.exception, schemaPrefix, services);
        Term excAtPostSV =
                createTermSV(appData.exceptionAtPost, schemaPrefix, services);
        Term heapSV =
                createTermSV(appData.heap, schemaPrefix, services);
        Term heapAtPreSV =
                createTermSV(appData.heapAtPre, schemaPrefix, services);
        Term heapAtPostSV =
                createTermSV(appData.heapAtPost, schemaPrefix, services);
        Term mbyAtPreSV =
                createTermSV(appData.mbyAtPre, schemaPrefix, services);
        return new ProofObligationVars(selfSV, selfAtPostSV, guardSV, localInSVs,
                                       guardAtPostSV, localOutSVs, resSV, resAtPostSV, excSV,
                                       excAtPostSV, heapSV, heapAtPreSV,
                                       heapAtPostSV, mbyAtPreSV, "", services, local);
    }


    private Taclet genInfFlowContractApplTaclet(ProofObligationVars appData,
                                                Services services,
                                                boolean local) {
        Name tacletName = generateName();

        // generate schemaFind and schemaAssumes terms
        ProofObligationVars schemaDataFind = generateApplicationDataSVs(
                "find_", appData, services, local);
        Term schemaFind = generateSchemaFind(schemaDataFind, services);
        ProofObligationVars schemaDataAssumes = generateApplicationDataSVs(
                "assumes_", appData, services, local);
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


    Term createTermSV(Term t,
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

    static void register(ProgramVariable pv,
                         Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    abstract Term buildContractApplications(ProofObligationVars contAppData,
                                            ProofObligationVars contAppData2,
                                            Services services);
}
