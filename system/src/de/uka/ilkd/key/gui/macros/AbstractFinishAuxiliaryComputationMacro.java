/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Pair;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;


/**
 *
 * @author christoph
 */
abstract class AbstractFinishAuxiliaryComputationMacro implements ProofMacro {

    static final TermBuilder TB = TermBuilder.DF;

    private static final String SCHEMA_PREFIX = "sv_";


    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }


    @Override
    public String getDescription() {
        return "Finish auxiliary computation.";
    }


    private static Term calculateResultingTerm(Proof proof,
                                               IFProofObligationVars ifVars,
                                               Goal initGoal) {
        final Term[] goalFormulas1 =
                buildExecution(ifVars.c1, ifVars.getMapFor(ifVars.c1),
                               proof.openGoals(), initGoal);
        final Term[] goalFormulas2 =
                buildExecution(ifVars.c2, ifVars.getMapFor(ifVars.c2),
                               proof.openGoals(), initGoal);

        Term composedStates = TB.ff();
        for (int i = 0; i < goalFormulas1.length; i++) {
            for (int j = i; j < goalFormulas2.length; j++) {
                final Term composedState = TB.and(goalFormulas1[i], goalFormulas2[j]);
                composedStates = TB.or(composedStates, composedState);
            }
        }
        return composedStates;
    }


    private static Term[] buildExecution(ProofObligationVars c,
                                         Map<Term, Term> vsMap,
                                         ImmutableList<de.uka.ilkd.key.proof.Goal> symbExecGoals,
                                         Goal initGoal) {
        Services services = initGoal.proof().getServices();
        final Term[] goalFormulas = buildFormulasFromGoals(symbExecGoals);
        // the built-in heap symbol has to be handled with care
        final HashMap<Operator, Boolean> doNotReplace = new HashMap<Operator, Boolean>();
        doNotReplace.put(TB.getBaseHeap(services).op(), Boolean.TRUE);
        final Term[] renamedGoalFormulas =
                renameVariablesAndSkolemConstants(goalFormulas, vsMap, doNotReplace,
                                                  c.postfix, initGoal);
        Term[] result = new Term[renamedGoalFormulas.length];
        for (int i = 0; i < renamedGoalFormulas.length; i++) {
            result[i] =
                    TB.applyElementary(services, c.pre.heap, renamedGoalFormulas[i]);
        }
        return result;
    }


    private static Term[] applyProgramRenamingsToSubs(Term term,
                                                      Map<ProgramVariable, ProgramVariable>
                                                                          progVarReplaceMap,
                                                      Map<Operator, Boolean> notReplaceMap,
                                                      String postfix,
                                                      Services services) {
        Term[] appliedSubs = null;
        if (term.subs() != null) {
            appliedSubs = new Term[term.subs().size()];
            for (int i = 0; i < appliedSubs.length; i++) {
                appliedSubs[i] = applyRenamingsToPrograms(term.sub(i),
                                                          progVarReplaceMap,
                                                          notReplaceMap,
                                                          postfix,
                                                          services);
            }
        }
        return appliedSubs;
    }


    private static Map<ProgramVariable, ProgramVariable>
                        extractProgramVarReplaceMap(Map<Term, Term> replaceMap) {
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                new HashMap<ProgramVariable, ProgramVariable>();
        for (final Term t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                progVarReplaceMap.put((ProgramVariable) t.op(),
                                      (ProgramVariable) replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }


    private static void insertBoundVarsIntoNotReplaceMap(Term term,
                                                         Map<Operator, Boolean> notReplaceMap) {
        if (term.boundVars() != null) {
            for (final QuantifiableVariable bv : term.boundVars()) {
                notReplaceMap.put(bv, Boolean.TRUE);
            }
        }
    }


    private static Term renameFormulasWithoutPrograms(Term term,
                                                      Map<Term, Term> replaceMap,
                                                      Map<Operator, Boolean> notReplaceMap,
                                                      String postfix,
                                                      Goal initGoal) {
        Services services = initGoal.proof().getServices();
        if (term == null) {
            return null;
        }

        if (replaceMap == null) {
            replaceMap = new HashMap<Term, Term>();
        }
        if (notReplaceMap == null) {
            notReplaceMap = new HashMap<Operator, Boolean>();
        }

        if (notReplaceMap.containsKey(term.op())) {
            return term;
        } else if (replaceMap.containsKey(term)) {
            return replaceMap.get(term);
        } else if (term.op() instanceof ParsableVariable) {
            assert term.subs().isEmpty();
            final ParsableVariable pv = (ParsableVariable) term.op();
            final Name newName =
                    VariableNameProposer.DEFAULT.getNewName(services,
                                                            new Name(pv.name() +
                                                                     postfix));
            final Operator renamedPv = pv.rename(newName);
            if (renamedPv instanceof ProgramVariable) {
                // for the taclet application dialog (which gets the declared
                // program variables in a strange way and not directly from the
                // namespace); adds it also to the namespace
                initGoal.addProgramVariable((ProgramVariable)renamedPv);
            } else {
                services.getNamespaces().programVariables().addSafely(renamedPv);
            }
            final Term pvTerm = TB.label(TermFactory.DEFAULT.createTerm(renamedPv),
                                         term.getLabels());
            replaceMap.put(term, pvTerm);
            return pvTerm;

        } else if (term.op() instanceof Function &&
                   ((Function) term.op()).isSkolemConstant()) {
            final Function f = (Function) term.op();
            final Name newName =
                    VariableNameProposer.DEFAULT.getNewName(services,
                                                            new Name(f.name() +
                                                                     postfix));
            final Function renamedF = f.rename(newName);
            services.getNamespaces().functions().addSafely(renamedF);
            final Term fTerm =
                    TB.label(TermFactory.DEFAULT.createTerm(renamedF),
                             term.getLabels());
            replaceMap.put(term, fTerm);
            return fTerm;
        } else if (term.op() instanceof ElementaryUpdate) {
            final ElementaryUpdate u = (ElementaryUpdate) term.op();
            final Term lhsTerm = TB.var(u.lhs());
            final Term renamedLhs = renameFormulasWithoutPrograms(lhsTerm,
                                                                  replaceMap,
                                                                  notReplaceMap,
                                                                  postfix,
                                                                  initGoal);
            final Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix, initGoal);
            final ElementaryUpdate renamedU =
                    ElementaryUpdate.getInstance((UpdateableOperator) renamedLhs.op());
            final Term uTerm = TB.label(TermFactory.DEFAULT.createTerm(renamedU, renamedSubs),
                                        term.getLabels());
            replaceMap.put(term, uTerm);
            return uTerm;
        } else {
            insertBoundVarsIntoNotReplaceMap(term, notReplaceMap);
            final Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix, initGoal);
            final Term renamedTerm =
                    TermFactory.DEFAULT.createTerm(term.op(), renamedSubs,
                                                   term.boundVars(),
                                                   term.javaBlock(),
                                                   term.getLabels());
            replaceMap.put(term, renamedTerm);
            return renamedTerm;
        }
    }


    private static JavaBlock renameJavaBlock(Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                             Term term, Services services) {
        final ProgVarReplaceVisitor paramRepl =
                new ProgVarReplaceVisitor(term.javaBlock().program(), progVarReplaceMap, services);
        paramRepl.start();
        final JavaBlock renamedJavaBlock =
                JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private static Term[] buildFormulasFromGoals(ImmutableList<Goal> symbExecGoals) {
        Term[] result = new Term[symbExecGoals.size()];
        int i = 0;
        for (final Goal symbExecGoal : symbExecGoals) {
            result[i] = buildFormulaFromGoal(symbExecGoal);
            i++;
        }
        return result;
    }


    private static Term buildFormulaFromGoal(Goal symbExecGoal) {
        Term result = TB.tt();
        for (final SequentFormula f : symbExecGoal.sequent().antecedent()) {
            result = TB.and(result, f.formula());
        }
        for (final SequentFormula f : symbExecGoal.sequent().succedent()) {
            result = TB.and(result, TB.not(f.formula()));
        }
        return result;
    }


    private static Term[] renameVariablesAndSkolemConstants(Term[] terms,
                                                            Map<Term, Term> replaceMap,
                                                            Map<Operator, Boolean> notReplaceMap,
                                                            String postfix,
                                                            Goal initGoal) {
        Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] =
                    renameVariablesAndSkolemConstants(terms[i], replaceMap,
                                                      notReplaceMap, postfix,
                                                      initGoal);
        }
        return result;
    }


    private static Term renameVariablesAndSkolemConstants(Term term,
                                                          Map<Term, Term> replaceMap,
                                                          Map<Operator, Boolean> notReplaceMap,
                                                          String postfix,
                                                          Goal initGoal) {
        final Term temp = renameFormulasWithoutPrograms(term, replaceMap,
                                                        notReplaceMap,
                                                        postfix,
                                                        initGoal);
        Services services = initGoal.proof().getServices();
        final Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                extractProgramVarReplaceMap(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap, notReplaceMap,
                                        postfix, services);
    }


    private static Term applyRenamingsToPrograms(Term term,
                                                 Map<ProgramVariable, ProgramVariable>
                                                                     progVarReplaceMap,
                                                 Map<Operator, Boolean> notReplaceMap,
                                                 String postfix,
                                                 Services services) {
        if (term != null) {
            final JavaBlock renamedJavaBlock =
                    renameJavaBlock(progVarReplaceMap, term, services);
            final Term[] appliedSubs =
                    applyProgramRenamingsToSubs(term, progVarReplaceMap,
                                                notReplaceMap, postfix,
                                                services);

            final Term renamedTerm =
                    TermFactory.DEFAULT.createTerm(term.op(), appliedSubs,
                                                   term.boundVars(),
                                                   renamedJavaBlock,
                                                   term.getLabels());
            return renamedTerm;
        } else {
            return null;
        }
    }


    private static Term[] renameSubs(Term term,
                                     Map<Term, Term> replaceMap,
                                     Map<Operator, Boolean> notReplaceMap,
                                     String postfix,
                                     Goal initGoal) {
        Term[] renamedSubs = null;
        if (term.subs() != null) {
            renamedSubs = new Term[term.subs().size()];
            for (int i = 0; i < renamedSubs.length; i++) {
                renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i),
                                                               replaceMap,
                                                               notReplaceMap,
                                                               postfix,
                                                               initGoal);
            }
        }
        return renamedSubs;
    }

    protected static IFProofObligationVars generateApplicationDataSVs(IFProofObligationVars ifVars,
                                                                      Services services) {
        return new IFProofObligationVars(
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c1, services),
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c2, services),
                ifVars.symbExecVars);
    }

    private static ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
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
                selfAtPreSV : createTermSV(poVars.post.self, schemaPrefix, services));

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

        Term guardAtPostSV = (poVars.pre.guard == poVars.post.guard) ? guardAtPreSV :
            createTermSV(poVars.post.guard, schemaPrefix, services);
        Term resAtPostSV = (poVars.post.result == null || poVars.post.result.op().equals(n)) ?
                null : createTermSV(poVars.post.result, schemaPrefix, services);
        Term excAtPostSV = (poVars.post.exception == null || poVars.post.exception.op().equals(n)) ?
                        null : createTermSV(poVars.post.exception, schemaPrefix, services);
        Term heapAtPostSV = (poVars.pre.heap == poVars.post.heap ?
                heapAtPreSV : createTermSV(poVars.post.heap, schemaPrefix, services));

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
        return new ProofObligationVars(pre, post);
    }

    private static Term createTermSV(Term t,
                                     String schemaPrefix,
                                     Services services) {
        if (t == null) {
            return null;
        }
        String svName = schemaPrefix + t.toString();
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        Sort sort = t.sort();
        return TB.var(SchemaVariableFactory.createTermSV(name, sort));
    }

    private static ImmutableList<Term> createTermSV(ImmutableList<Term> ts,
                                                    String schemaPrefix,
                                                    Services services) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term t : ts) {
            result = result.append(createTermSV(t, schemaPrefix, services));
        }
        return result;
    }

    protected static final Term calculateResultingSVTerm(Proof proof,
                                                         IFProofObligationVars origVars,
                                                         IFProofObligationVars schemaVars,
                                                         Goal initGoal) {
        final Term term = calculateResultingTerm(proof, origVars, initGoal);
        return replace(term, origVars, schemaVars);
    }

    private static final Term replace(Term term,
                                      IFProofObligationVars origVars,
                                      IFProofObligationVars schemaVars) {
        Term intermediateResult = replace(term, origVars.c1, schemaVars.c1);
        return replace(intermediateResult, origVars.c2, schemaVars.c2);
    }

    private static final Term replace(Term term,
                                      ProofObligationVars origVars,
                                      ProofObligationVars schemaVars) {
        Term intermediateResult = replace(term, origVars.pre, schemaVars.pre);
        return replace(intermediateResult, origVars.post, schemaVars.post);
    }

    private static final Term replace(Term term,
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

    private static Pair<StateVars, StateVars> filter(StateVars origVars,
                                                     StateVars schemaVars) {
        schemaVars = filterSchemaVars(origVars, schemaVars);
        origVars = filterSchemaVars(schemaVars, origVars);
        return new Pair<StateVars, StateVars> (origVars, schemaVars);
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

    protected static void addContractApplicationTaclets(Goal initiatingGoal,
                                                        Proof symbExecProof) {
        final ImmutableList<Goal> openGoals = symbExecProof.openGoals();
        for (final Goal openGoal : openGoals) {
            final ImmutableSet<NoPosTacletApp> ruleApps =
                    openGoal.indexOfTaclets().allNoPosTacletApps();
            for (final NoPosTacletApp ruleApp : ruleApps) {
                final Taclet t = ruleApp.taclet();
                if (t.getSurviveSymbExec()) {
                    initiatingGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
                }
            }
        }
    }
}