/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;


/**
 *
 * @author christoph
 */
public class RemovePostTacletBuilder extends AbstractInfFlowTacletBuilder {

    public static final Name REMOVE_POST_RULENAME = new Name("Remove_post");

    static final TermBuilder TB = TermBuilder.DF;

    private static final String SCHEMA_PREFIX = "sv_";


    public RemovePostTacletBuilder(Services services) {
        super(services);
    }


    public ArrayList<Taclet> generateTaclets(Term post,
                                             IFProofObligationVars ifVars,
                                             Services services) {
        ArrayList<Term> postParts = extractPostParts(post, services);
        IFProofObligationVars ifSchemaVars = generateApplicationDataSVs(ifVars, services);
        ArrayList<Term> svPostParts = new ArrayList<Term>(postParts.size());
        for (Term term: postParts) {
            svPostParts.add(replace(term, ifVars, ifSchemaVars));
        }
        postParts = svPostParts;
        ArrayList<Taclet> removePostTaclets = new ArrayList<Taclet>();
        int i = 0;
        for (Term postPart : postParts) {
            // collect quantifaible variables of the postPart and replace them
            // by schema variables
            Map<QuantifiableVariable, SchemaVariable> quantifiableVarsToSchemaVars =
                    collectQuantifiableVariables(postPart, services);
            final OpReplacer or = new OpReplacer(quantifiableVarsToSchemaVars);
            postPart = or.replace(postPart);


            RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
            tacletBuilder.setName(new Name(REMOVE_POST_RULENAME + "_" + i));
            tacletBuilder.setFind(postPart);
            tacletBuilder.setApplicationRestriction(RewriteTaclet.SUCCEDENT_POLARITY);
            tacletBuilder.setSurviveSmbExec(false);
            RewriteTacletGoalTemplate goal =
                    new RewriteTacletGoalTemplate(TermBuilder.DF.ff());
            tacletBuilder.addTacletGoalTemplate(goal);
            tacletBuilder.addRuleSet(new RuleSet(new Name("information_flow_contract_appl")));
            addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values(), ifSchemaVars.c1);
            addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values(), ifSchemaVars.c2);

            removePostTaclets.add(tacletBuilder.getTaclet());
        }
        return removePostTaclets;
    }


    private ArrayList<Term> extractPostParts(Term post, Services services) {
        Function newIso =
                (Function)services.getNamespaces().functions().lookup("newObjectsIsomorphic");
        ArrayList<Term> postParts = new ArrayList<Term>();
        if (post.op() == Junctor.IMP) {
            postParts.add(post.sub(1));
        } else if (post.op() == Junctor.AND) {
            postParts.addAll(extractPostParts(post.sub(0), services));
            postParts.addAll(extractPostParts(post.sub(1), services));
        } else if (post.depth() == 1 || post.op() == Junctor.TRUE ||
                   post.op() == newIso || post.op() == Equality.EQUALS) {
            // do nothing
        } else {
            throw new IllegalArgumentException("error while extracting post " +
                                               "parts: information flow post " +
                                               "term malformed: " + post);
        }
        return postParts;
    }


    private final Term replace(Term term,
                                      IFProofObligationVars origVars,
                                      IFProofObligationVars schemaVars) {
        Term intermediateResult = replace(term, origVars.c1, schemaVars.c1);
        return replace(intermediateResult, origVars.c2, schemaVars.c2);
    }


    private final Term replace(Term term,
                                      ProofObligationVars origVars,
                                      ProofObligationVars schemaVars) {
        Term intermediateResult = replace(term, origVars.pre, schemaVars.pre);
        return replace(intermediateResult, origVars.post, schemaVars.post);
    }


    private final Term replace(Term term,
                                      StateVars origVars,
                                      StateVars schemaVars) {
        de.uka.ilkd.key.util.LinkedHashMap<Term, Term> map =
                new de.uka.ilkd.key.util.LinkedHashMap<Term, Term>();

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
        OpReplacer or = new OpReplacer(map);
        Term result = or.replace(term);

        return result;
    }


    private Pair<StateVars, StateVars> filter(StateVars origVars,
                                                     StateVars schemaVars) {
        schemaVars = filterSchemaVars(origVars, schemaVars);
        origVars = filterSchemaVars(schemaVars, origVars);
        return new Pair<StateVars, StateVars> (origVars, schemaVars);
    }


    private StateVars filterSchemaVars(StateVars origVars,
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


    private IFProofObligationVars generateApplicationDataSVs(IFProofObligationVars ifVars,
                                                                    Services services) {
        return new IFProofObligationVars(
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c1, services),
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c2, services),
                ifVars.symbExecVars);
    }


    private ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
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
                null;
        //createTermSV(appData.pre.result, schemaPrefix, services);
        Term excAtPreSV =
                null;
        //createTermSV(appData.pre.exception, schemaPrefix, services);
        Term heapAtPreSV =
                createTermSV(appData.pre.heap, schemaPrefix, services);
        Term mbyAtPreSV =
                createTermSV(appData.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        Term selfAtPostSV = (appData.pre.self == appData.post.self ?
                selfAtPreSV : createTermSV(appData.post.self, schemaPrefix, services));

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
                guardAtPreSV : createTermSV(appData.post.guard, schemaPrefix, services));
        Term resAtPostSV = //(appData.pre.result == appData.post.result ? resAtPreSV :
                createTermSV(appData.post.result, schemaPrefix, services);//);
        Term excAtPostSV = //(appData.pre.exception == appData.post.exception ? excAtPreSV :
                createTermSV(appData.post.exception, schemaPrefix, services);//);
        Term heapAtPostSV = (appData.pre.heap == appData.post.heap ?
                heapAtPreSV : createTermSV(appData.post.heap, schemaPrefix, services));

        // build state variable container for pre and post state
        StateVars pre =
                new StateVars(selfAtPreSV, guardAtPreSV, localVarsAtPreSVs, resAtPreSV,
                        excAtPreSV, heapAtPreSV, mbyAtPreSV);
        pre = filterSchemaVars(appData.pre, pre);
        StateVars post =
                new StateVars(selfAtPostSV, guardAtPostSV, localVarsAtPostSVs, resAtPostSV,
                        excAtPostSV, heapAtPostSV, null);
        post = filterSchemaVars(appData.post, post);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post);
    }
}