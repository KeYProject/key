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
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.tacletbuilder.InfFlowTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.MiscTools;
import java.util.Iterator;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
abstract class AbstractInfFlowContractTacletBuilder extends TermBuilder.Serviced {

    private Term[] contextUpdates;
    private Term contractSelfAtPre;
    private Term contractSelfAtPost;
    private ImmutableList<Term> localVarsAtPre;
    private Term heapAtPre;
    private ImmutableList<Term> localVarsAtPost;
    private Term contractResultAtPre;
    private Term contractResultAtPost;
    private Term exceptionVarAtPre;
    private Term exceptionVarAtPost;
    private Term heapAtPost;
    private Term loopGuardAtPre;
    private Term loopGuardAtPost;
    private Term mbyAtPre;


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


    public void setSelfAtPre(Term contractSelf) {
        this.contractSelfAtPre = contractSelf;
    }
    
    public void setSelfAtPost(Term contractSelfAtPost) {
        this.contractSelfAtPost = contractSelfAtPost;
    }

    public void setGuard(Term guard) {
        this.loopGuardAtPre = guard;
    }

    public void setGuardAtPost(Term guardAtPost) {
        this.loopGuardAtPost = guardAtPost;
    }

    public void setLocalVarsAtPre(ImmutableList<Term> localVarsAtPre) {
        this.localVarsAtPre = localVarsAtPre;
    }

    public void setLocalVarsAtPost(ImmutableList<Term> localVarsAtPost) {
        this.localVarsAtPost = localVarsAtPost;
    }

    public void setResultAtPre(Term contractResult) {
        this.contractResultAtPre = contractResult;
    }

    public void setResultAtPost(Term resultAtPost) {
        this.contractResultAtPost = resultAtPost;
    }

    public void setExceptionAtPre(Term exceptionVar) {
        this.exceptionVarAtPre = exceptionVar;
    }

    public void setExceptionAtPost(Term exceptionAtPost) {
        this.exceptionVarAtPost = exceptionAtPost;
    }

    public void setMbyAtPre(Term mby) {
        this.mbyAtPre = mby;
    }

    public Term buildContractApplPredTerm() {
        ProofObligationVars appData = getProofObligationVars();
        Term contractApplPredTerm = getContractApplPred(appData);
        for (Term update : contextUpdates) {
            contractApplPredTerm = apply(update, contractApplPredTerm);
        }
        return contractApplPredTerm;
    }


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
        StateVars pre =
                new StateVars(contractSelfAtPre, loopGuardAtPre, localVarsAtPre,
                              contractResultAtPre, exceptionVarAtPre, heapAtPre,
                              mbyAtPre);
        StateVars post =
                new StateVars(contractSelfAtPost, loopGuardAtPost, localVarsAtPost,
                              contractResultAtPost, exceptionVarAtPost, heapAtPost);
        assert pre.paddedTermList.size() == post.paddedTermList.size();
        return new ProofObligationVars(pre, post);
    }


    abstract Term getContractApplPred(ProofObligationVars appData);


    ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
                                                   ProofObligationVars appData,
                                                   Services services) {
        // generate a new schema variable for any pre variable
        Term selfAtPreSV =
                createTermSV(appData.pre.self, schemaPrefix, services);
        ImmutableList<Term> localVarsAtPreSVs =
                createTermSV(appData.pre.localVars, schemaPrefix, services);
        Term guardAtPreSV =
                createTermSV(appData.pre.guard, schemaPrefix, services);
        Term resAtPreSV =
                createTermSV(appData.pre.result, schemaPrefix, services);
        Term excAtPreSV =
                createTermSV(appData.pre.exception, schemaPrefix, services);
        Term heapAtPreSV =
                createTermSV(appData.pre.heap, schemaPrefix, services);
        Term mbyAtPreSV =
                createTermSV(appData.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        Term selfAtPostSV = (appData.pre.self == appData.post.self ?
                selfAtPreSV :
                createTermSV(appData.post.self, schemaPrefix, services));

        ImmutableList<Term> localVarsAtPostSVs = ImmutableSLList.<Term>nil();
        Iterator<Term> appDataPreLocalVarsIt = appData.pre.localVars.iterator();
        Iterator<Term> schemaLocalVarsAtPreIt = localVarsAtPreSVs.iterator();
        for (Term appDataPostLocalVar : appData.post.localVars) {
            Term appDataPreLocalVar = appDataPreLocalVarsIt.next();
            Term localPreVar = schemaLocalVarsAtPreIt.next();
            if (appDataPostLocalVar == appDataPreLocalVar) {
                localVarsAtPostSVs = localVarsAtPostSVs.append(localPreVar);
            } else {
                localVarsAtPostSVs =
                        localVarsAtPostSVs.append(createTermSV(appDataPostLocalVar,
                                                               schemaPrefix,
                                                               services));
            }
        }

        Term guardAtPostSV = (appData.pre.guard == appData.post.guard ?
                guardAtPreSV :
                createTermSV(appData.post.guard, schemaPrefix, services));
        Term resAtPostSV = (appData.pre.result == appData.post.result ?
                resAtPreSV :
                createTermSV(appData.post.result, schemaPrefix, services));
        Term excAtPostSV = (appData.pre.exception == appData.post.exception ?
                excAtPreSV :
                createTermSV(appData.post.exception, schemaPrefix, services));
        Term heapAtPostSV = (appData.pre.heap == appData.post.heap ?
                heapAtPreSV :
                createTermSV(appData.post.heap, schemaPrefix, services));

        // build state vararibale container for pre and post state
        StateVars pre =
                new StateVars(selfAtPreSV, guardAtPreSV,
                              localVarsAtPreSVs, resAtPreSV,
                              excAtPreSV, heapAtPreSV,
                              mbyAtPreSV);
        StateVars post =
                new StateVars(selfAtPostSV, guardAtPostSV,
                              localVarsAtPostSVs, resAtPostSV,
                              excAtPostSV, heapAtPostSV,
                              null);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post);
    }


    private Taclet genInfFlowContractApplTaclet(ProofObligationVars appData,
                                                Services services) {
        Name tacletName = generateName();

        // generate schemaFind and schemaAssumes terms
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


    Term createTermSV(Term t,
                      String schemaPrefix,
                      Services services) {
        if (t == null) {
            return null;
        }
        String svName = MiscTools.toValidVariableName(schemaPrefix + t.toString()).toString();
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
