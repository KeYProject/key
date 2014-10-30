// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;
import java.util.Iterator;
import java.util.Map;


/**
 * Builds the rule which inserts information flow contract applications.
 * <p/>
 * @author christoph
 */
abstract class AbstractInfFlowUnfoldTacletBuilder extends AbstractInfFlowTacletBuilder {

    private static final String SCHEMA_PREFIX = "sv_";
    static final String UNFOLD = "unfold computed formula ";

    /** Counter to allow several side-proofs. */
    static int unfoldCounter = 0;

    private IFProofObligationVars ifVars;

    private Term replacewith;


    public AbstractInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setInfFlowVars(IFProofObligationVars ifVars) {
        this.ifVars = ifVars.labelHeapAtPreAsAnonHeapFunc();
    }


    public void setReplacewith(Term replacewith) {
        this.replacewith = replacewith;
    }


    public Taclet buildTaclet() {
        Name tacletName = getTacletName();
        unfoldCounter++;

        // create schema vars
        IFProofObligationVars schemaVars =
                generateApplicationDataSVs(ifVars, services);

        // create find term and replace information flow variables by
        // schema variables
        final Term find = createFindTerm(ifVars);
        Term schemaFind = replace(find, ifVars, schemaVars, services);

        // create replacewith term and replace information flow variables by
        // schema variables in the replacewith term, too
        Term schemaReplaceWith = replace(replacewith, ifVars, schemaVars, services);

        // collect quantifiable variables of the find term and replacewith term
        // and replace all quantifiable variables by schema variables
        Map<QuantifiableVariable, SchemaVariable> quantifiableVarsToSchemaVars =
                collectQuantifiableVariables(schemaFind, services);
        quantifiableVarsToSchemaVars.putAll(
                collectQuantifiableVariables(schemaReplaceWith, services));
	final OpReplacer or = new OpReplacer(quantifiableVarsToSchemaVars, tf());
	schemaFind = or.replace(schemaFind);
	schemaReplaceWith = or.replace(schemaReplaceWith);

        //create taclet
        final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.ANTECEDENT_POLARITY);
        final RewriteTacletGoalTemplate goal =
                new RewriteTacletGoalTemplate(schemaReplaceWith);
        tacletBuilder.addTacletGoalTemplate(goal);
        tacletBuilder.addRuleSet(new RuleSet(new Name("concrete")));
        tacletBuilder.setSurviveSmbExec(true);
        addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values());

        return tacletBuilder.getTaclet();
    }


    private IFProofObligationVars generateApplicationDataSVs(
            IFProofObligationVars ifVars,
            Services services) {
        return new IFProofObligationVars(
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c1, services),
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c2, services),
                ifVars.symbExecVars);
    }


    private ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
                                                           ProofObligationVars poVars,
                                                           Services services) {
        Function n = services.getTypeConverter().getHeapLDT().getNull();

        // generate a new schema variable for any pre variable
        Term selfAtPreSV =
                createTermSV(poVars.pre.self, schemaPrefix, services);
        ImmutableList<Term> localVarsAtPreSVs =
                createTermSV(poVars.pre.localVars, schemaPrefix, services);
        Term guardAtPreSV =
                createTermSV(poVars.pre.guard, schemaPrefix, services);
        Term resAtPreSV = null;
        Term excAtPreSV = null;
        Term heapAtPreSV =
                createTermSV(poVars.pre.heap, schemaPrefix, services);
        Term mbyAtPreSV =
                createTermSV(poVars.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        Term selfAtPostSV = (poVars.pre.self == poVars.post.self ?
                             selfAtPreSV :
                             createTermSV(poVars.post.self, schemaPrefix, services));

        ImmutableList<Term> localVarsAtPostSVs = ImmutableSLList.<Term>nil();
        Iterator<Term> appDataPreLocalVarsIt = poVars.pre.localVars.iterator();
        Iterator<Term> schemaLocalVarsAtPreIt = localVarsAtPreSVs.iterator();
        for (Term appDataPostLocalVar : poVars.post.localVars) {
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

        Term guardAtPostSV = (poVars.pre.guard == poVars.post.guard) ?
                             guardAtPreSV :
                             createTermSV(poVars.post.guard, schemaPrefix, services);
        Term resAtPostSV = (poVars.post.result == null ||
                            poVars.post.result.op().equals(n)) ?
                           null :
                           createTermSV(poVars.post.result, schemaPrefix, services);
        Term excAtPostSV = (poVars.post.exception == null ||
                            poVars.post.exception.op().equals(n)) ?
                           null :
                           createTermSV(poVars.post.exception, schemaPrefix, services);
        Term heapAtPostSV = (poVars.pre.heap == poVars.post.heap ?
                             heapAtPreSV :
                             createTermSV(poVars.post.heap, schemaPrefix, services));

        // build state variable container for pre and post state
        StateVars pre =
                new StateVars(selfAtPreSV, guardAtPreSV, localVarsAtPreSVs, resAtPreSV,
                              excAtPreSV, heapAtPreSV, mbyAtPreSV);
        pre = filterSchemaVars(poVars.pre, pre);
        StateVars post =
                new StateVars(selfAtPostSV, guardAtPostSV, localVarsAtPostSVs, resAtPostSV,
                              excAtPostSV, heapAtPostSV, null);
        post = filterSchemaVars(poVars.post, post);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post, poVars.exceptionParameter,
                                       poVars.formalParams, services);
    }


    private static Term replace(Term term,
                                IFProofObligationVars origVars,
                                IFProofObligationVars schemaVars,
                                Services services) {
        Term intermediateResult = replace(term, origVars.c1, schemaVars.c1, services);
        return replace(intermediateResult, origVars.c2, schemaVars.c2, services);
    }


    private static Term replace(Term term,
                                ProofObligationVars origVars,
                                ProofObligationVars schemaVars,
                                Services services) {
        Term intermediateResult = replace(term, origVars.pre, schemaVars.pre, services);
        return replace(intermediateResult, origVars.post, schemaVars.post, services);
    }


    private static Term replace(Term term,
                                StateVars origVars,
                                StateVars schemaVars,
                                Services services) {
        LinkedHashMap<Term, Term> map = new LinkedHashMap<Term, Term>();

        Pair<StateVars, StateVars> vars = filter(origVars, schemaVars);
        origVars = vars.first;
        schemaVars = vars.second;
        assert origVars.termList.size() == schemaVars.termList.size();
        Iterator<Term> origVarsIt = origVars.termList.iterator();
        Iterator<Term> schemaVarsIt = schemaVars.termList.iterator();
        while (origVarsIt.hasNext()) {
            Term origTerm = origVarsIt.next();
            Term svTerm = schemaVarsIt.next();
            if (origTerm != null && svTerm != null) {
                assert svTerm.sort().equals(origTerm.sort()) ||
                       svTerm.sort().extendsSorts().contains(origTerm.sort()) :
                        "mismatch of sorts: orignal term " + origTerm +
                        ", sort " + origTerm.sort() +
                        "; replacement term" + svTerm + ", sort " +
                        svTerm.sort();
                map.put(origTerm, svTerm);
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        Term result = or.replace(term);

        return result;
    }


    private static Pair<StateVars, StateVars> filter(StateVars origVars,
                                                     StateVars schemaVars) {
        schemaVars = filterSchemaVars(origVars, schemaVars);
        origVars = filterSchemaVars(schemaVars, origVars);
        return new Pair<StateVars, StateVars>(origVars, schemaVars);
    }


    private static StateVars filterSchemaVars(StateVars origVars,
                                              StateVars schemaVars) {
        if (origVars.termList.size() == schemaVars.termList.size()) {
            return schemaVars;
        }
        Term self = schemaVars.self;
        Term guard = schemaVars.guard;
        ImmutableList<Term> localVars = schemaVars.localVars;
        Term result = schemaVars.result;
        Term exception = schemaVars.exception;
        Term heap = schemaVars.heap;
        Term mbyAtPre = schemaVars.mbyAtPre;
        if (origVars.self == null) {
            self = null;
        }
        if (origVars.guard == null) {
            guard = null;
        }
        if (origVars.localVars == null) {
            localVars = null;
        } else if (origVars.localVars.isEmpty()) {
            localVars = ImmutableSLList.<Term>nil();
        }
        if (origVars.result == null) {
            result = null;
        }
        if (origVars.exception == null) {
            exception = null;
        }
        if (origVars.heap == null) {
            heap = null;
        }
        if (origVars.mbyAtPre == null) {
            mbyAtPre = null;
        }
        return new StateVars(self, guard, localVars, result, exception, heap, mbyAtPre);
    }


    abstract Name getTacletName();


    abstract Term createFindTerm(IFProofObligationVars ifVars);
}
