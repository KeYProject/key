/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.RuleSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;


/**
 * Builds the rule which inserts information flow contract applications.
 * <p/>
 *
 * @author christoph
 */
abstract class AbstractInfFlowUnfoldTacletBuilder extends AbstractInfFlowTacletBuilder {

    private static final String SCHEMA_PREFIX = "sv_";
    static final String UNFOLD = "unfold computed formula ";

    /** Counter to allow several side-proofs. */
    static int unfoldCounter = 0;

    private IFProofObligationVars ifVars;

    private JTerm replacewith;


    protected AbstractInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setInfFlowVars(IFProofObligationVars ifVars) {
        this.ifVars = ifVars.labelHeapAtPreAsAnonHeapFunc();
    }


    public void setReplacewith(JTerm replacewith) {
        this.replacewith = replacewith;
    }


    public Taclet buildTaclet() {
        Name tacletName = getTacletName();
        unfoldCounter++;

        // create schema vars
        IFProofObligationVars schemaVars = generateApplicationDataSVs(ifVars, services);

        // create find term and replace information flow variables by
        // schema variables
        final JTerm find = createFindTerm(ifVars);

        JTerm schemaFind = replace(find, ifVars, schemaVars, services);

        // create replacewith term and replace information flow variables by
        // schema variables in the replacewith term, too
        JTerm schemaReplaceWith = replace(replacewith, ifVars, schemaVars, services);

        // collect quantifiable variables of the find term and replacewith term
        // and replace all quantifiable variables by schema variables
        Map<QuantifiableVariable, VariableSV> quantifiableVarsToSchemaVars =
            collectQuantifiableVariables(schemaFind, services);
        quantifiableVarsToSchemaVars
                .putAll(collectQuantifiableVariables(schemaReplaceWith, services));
        final OpReplacer or = new OpReplacer(quantifiableVarsToSchemaVars, tf());
        schemaFind = or.replace(schemaFind);
        schemaReplaceWith = or.replace(schemaReplaceWith);

        // create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder =
            new RewriteTacletBuilder<>();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind);
        tacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.ANTECEDENT_POLARITY));
        final RewriteTacletGoalTemplate goal = new RewriteTacletGoalTemplate(schemaReplaceWith);
        tacletBuilder.addTacletGoalTemplate(goal);
        tacletBuilder.addRuleSet(new RuleSet(new Name("concrete")));
        tacletBuilder.setSurviveSmbExec(true);
        addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values());

        return tacletBuilder.getTaclet();
    }


    private IFProofObligationVars generateApplicationDataSVs(IFProofObligationVars ifVars,
            Services services) {
        return new IFProofObligationVars(
            generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c1, services),
            generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c2, services), ifVars.symbExecVars);
    }


    private ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
            ProofObligationVars poVars, Services services) {
        Function n = services.getTypeConverter().getHeapLDT().getNull();

        // generate a new schema variable for any pre variable
        JTerm selfAtPreSV = createTermSV(poVars.pre.self, schemaPrefix, services);
        ImmutableList<JTerm> localVarsAtPreSVs =
            createTermSV(poVars.pre.localVars, schemaPrefix, services);
        JTerm guardAtPreSV = createTermSV(poVars.pre.guard, schemaPrefix, services);
        JTerm resAtPreSV = null;
        JTerm excAtPreSV = null;
        JTerm heapAtPreSV = createTermSV(poVars.pre.heap, schemaPrefix, services);
        JTerm mbyAtPreSV = createTermSV(poVars.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        JTerm selfAtPostSV = (poVars.pre.self == poVars.post.self ? selfAtPreSV
                : createTermSV(poVars.post.self, schemaPrefix, services));

        ImmutableList<JTerm> localVarsAtPostSVs = ImmutableSLList.nil();
        Iterator<JTerm> appDataPreLocalVarsIt = poVars.pre.localVars.iterator();
        Iterator<JTerm> schemaLocalVarsAtPreIt = localVarsAtPreSVs.iterator();
        for (JTerm appDataPostLocalVar : poVars.post.localVars) {
            JTerm appDataPreLocalVar = appDataPreLocalVarsIt.next();
            JTerm localPreVar = schemaLocalVarsAtPreIt.next();
            if (appDataPostLocalVar == appDataPreLocalVar) {
                localVarsAtPostSVs = localVarsAtPostSVs.append(localPreVar);
            } else {
                localVarsAtPostSVs = localVarsAtPostSVs
                        .append(createTermSV(appDataPostLocalVar, schemaPrefix, services));
            }
        }

        JTerm guardAtPostSV = (poVars.pre.guard == poVars.post.guard) ? guardAtPreSV
                : createTermSV(poVars.post.guard, schemaPrefix, services);
        JTerm resAtPostSV = (poVars.post.result == null || poVars.post.result.op().equals(n)) ? null
                : createTermSV(poVars.post.result, schemaPrefix, services);
        JTerm excAtPostSV =
            (poVars.post.exception == null || poVars.post.exception.op().equals(n)) ? null
                    : createTermSV(poVars.post.exception, schemaPrefix, services);
        JTerm heapAtPostSV = (poVars.pre.heap == poVars.post.heap ? heapAtPreSV
                : createTermSV(poVars.post.heap, schemaPrefix, services));

        // build state variable container for pre and post state
        StateVars pre = new StateVars(selfAtPreSV, guardAtPreSV, localVarsAtPreSVs, resAtPreSV,
            excAtPreSV, heapAtPreSV, mbyAtPreSV);
        pre = filterSchemaVars(poVars.pre, pre);
        StateVars post = new StateVars(selfAtPostSV, guardAtPostSV, localVarsAtPostSVs, resAtPostSV,
            excAtPostSV, heapAtPostSV, null);
        post = filterSchemaVars(poVars.post, post);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post, poVars.exceptionParameter, poVars.formalParams,
            services);
    }


    private static JTerm replace(JTerm term, IFProofObligationVars origVars,
            IFProofObligationVars schemaVars, Services services) {
        JTerm intermediateResult = replace(term, origVars.c1, schemaVars.c1, services);
        return replace(intermediateResult, origVars.c2, schemaVars.c2, services);
    }


    private static JTerm replace(JTerm term, ProofObligationVars origVars,
            ProofObligationVars schemaVars, Services services) {
        JTerm intermediateResult = replace(term, origVars.pre, schemaVars.pre, services);
        return replace(intermediateResult, origVars.post, schemaVars.post, services);
    }


    private static JTerm replace(JTerm term, StateVars origVars, StateVars schemaVars,
            Services services) {
        LinkedHashMap<JTerm, JTerm> map = new LinkedHashMap<>();

        Pair<StateVars, StateVars> vars = filter(origVars, schemaVars);
        origVars = vars.first;
        schemaVars = vars.second;
        assert origVars.termList.size() == schemaVars.termList.size();
        Iterator<JTerm> origVarsIt = origVars.termList.iterator();
        Iterator<JTerm> schemaVarsIt = schemaVars.termList.iterator();
        while (origVarsIt.hasNext()) {
            JTerm origTerm = origVarsIt.next();
            JTerm svTerm = schemaVarsIt.next();
            if (origTerm != null && svTerm != null) {
                assert svTerm.sort().equals(origTerm.sort())
                        || svTerm.sort().extendsSorts().contains(origTerm.sort())
                        : "mismatch of sorts: orignal term " + origTerm + ", sort "
                            + origTerm.sort() + "; replacement term" + svTerm + ", sort "
                            + svTerm.sort();
                map.put(origTerm, svTerm);
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        term = TermLabelManager.removeIrrelevantLabels(term, services.getTermFactory());
        JTerm result = or.replace(term);

        return result;
    }


    private static Pair<StateVars, StateVars> filter(StateVars origVars, StateVars schemaVars) {
        schemaVars = filterSchemaVars(origVars, schemaVars);
        origVars = filterSchemaVars(schemaVars, origVars);
        return new Pair<>(origVars, schemaVars);
    }


    private static StateVars filterSchemaVars(StateVars origVars, StateVars schemaVars) {
        if (origVars.termList.size() == schemaVars.termList.size()) {
            return schemaVars;
        }
        JTerm self = schemaVars.self;
        JTerm guard = schemaVars.guard;
        ImmutableList<JTerm> localVars = schemaVars.localVars;
        JTerm result = schemaVars.result;
        JTerm exception = schemaVars.exception;
        JTerm heap = schemaVars.heap;
        JTerm mbyAtPre = schemaVars.mbyAtPre;
        if (origVars.self == null) {
            self = null;
        }
        if (origVars.guard == null) {
            guard = null;
        }
        if (origVars.localVars == null) {
            localVars = null;
        } else if (origVars.localVars.isEmpty()) {
            localVars = ImmutableSLList.nil();
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


    abstract JTerm createFindTerm(IFProofObligationVars ifVars);
}
