/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;

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


    protected Term calculateResultingTerm(Proof proof,
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


    private Term[] buildExecution(ProofObligationVars c,
                                  Map<Term, Term> vsMap,
                                  ImmutableList<de.uka.ilkd.key.proof.Goal> symbExecGoals,
                                  Goal initGoal) {
        Services services = initGoal.proof().getServices();
        final Term[] goalFormulas = buildFormulasFromGoals(symbExecGoals);
        // the built-in heap symbol has to be handled with care
        final HashMap<Operator, Boolean> doNotReplace =
                new HashMap<Operator, Boolean>();
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


    private Term[] applyProgramRenamingsToSubs(Term term,
                                               Map<ProgramVariable, AbstractSortedOperator>
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


    private Map<ProgramVariable, AbstractSortedOperator>
                    extractProgramVarReplaceMap(Map<Term, Term> replaceMap) {
        Map<ProgramVariable, AbstractSortedOperator> progVarReplaceMap =
                new HashMap<ProgramVariable, AbstractSortedOperator>();
        for (final Term t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                if (!(replaceMap.get(t).op() instanceof AbstractSortedOperator)) {
                    ProgramSV sv =
                            SchemaVariableFactory.createProgramSV(
                                    new ProgramElementName(replaceMap.get(t).op().name().toString()),
                                    ProgramSVSort.VARIABLE, false);
                    System.out.println("extractProgramVarReplaceMap:" + '\n' +
                                       sv.toString() + " :: " + sv.sort().toString());
                    //replaceMap.put(t, TB.var(sv));
                }
            progVarReplaceMap.put((ProgramVariable) t.op(),
                                  (AbstractSortedOperator) replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }


    private void insertBoundVarsIntoNotReplaceMap(Term term,
                                                  Map<Operator, Boolean> notReplaceMap) {
        if (term.boundVars() != null) {
            for (final QuantifiableVariable bv : term.boundVars()) {
                notReplaceMap.put(bv, Boolean.TRUE);
            }
        }
    }


    private Term renameFormulasWithoutPrograms(Term term,
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
            final Term pvTerm = TermFactory.DEFAULT.createTerm(renamedPv);
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
                    TermFactory.DEFAULT.createTerm(renamedF);
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
            final UpdateableOperator lhs;
            if (renamedLhs.op() instanceof UpdateableOperator) {
                lhs = (UpdateableOperator) renamedLhs.op();
            } else {
                lhs = SchemaVariableFactory.createProgramSV(
                        (VariableNamer.parseName(renamedLhs.op().name().toString())),
                        ProgramSVSort.VARIABLE, false);
                System.out.println(renamedLhs.toString() + " :: " +
                                   renamedLhs.sort().toString() + " -> " +
                                   lhs.toString() + " :: " + lhs.sort().toString());
            }
            final ElementaryUpdate renamedU = ElementaryUpdate.getInstance(lhs);
            final Term uTerm = TermFactory.DEFAULT.createTerm(renamedU, renamedSubs);
            replaceMap.put(term, uTerm);
            return uTerm;
        } else {
            insertBoundVarsIntoNotReplaceMap(term, notReplaceMap);
            final Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix, initGoal);
            final Term renamedTerm =
                    TermFactory.DEFAULT.createTerm(term.op(), renamedSubs,
                                                   term.boundVars(),
                                                   term.javaBlock());
            replaceMap.put(term, renamedTerm);
            return renamedTerm;
        }
    }


    private JavaBlock renameJavaBlock(Map<ProgramVariable, AbstractSortedOperator> progVarReplaceMap,
                                      Term term, Services services) {
        final ProgVarSchemaVarReplaceVisitor paramRepl =
                new ProgVarSchemaVarReplaceVisitor(term.javaBlock().program(),
                                                   progVarReplaceMap,
                                                   services);
        paramRepl.start();
        final JavaBlock renamedJavaBlock =
                JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private Term[] buildFormulasFromGoals(ImmutableList<Goal> symbExecGoals) {
        Term[] result = new Term[symbExecGoals.size()];
        int i = 0;
        for (final Goal symbExecGoal : symbExecGoals) {
            result[i] = buildFormulaFromGoal(symbExecGoal);
            i++;
        }
        return result;
    }


    private Term buildFormulaFromGoal(Goal symbExecGoal) {
        Term result = TB.tt();
        for (final SequentFormula f : symbExecGoal.sequent().antecedent()) {
            result = TB.and(result, f.formula());
        }
        for (final SequentFormula f : symbExecGoal.sequent().succedent()) {
            result = TB.and(result, TB.not(f.formula()));
        }
        return result;
    }


    private Term[] renameVariablesAndSkolemConstants(Term[] terms,
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


    private Term renameVariablesAndSkolemConstants(Term term,
                                                   Map<Term, Term> replaceMap,
                                                   Map<Operator, Boolean> notReplaceMap,
                                                   String postfix,
                                                   Goal initGoal) {
        final Term temp = renameFormulasWithoutPrograms(term, replaceMap,
                                                        notReplaceMap,
                                                        postfix,
                                                        initGoal);
        Services services = initGoal.proof().getServices();
        final Map<ProgramVariable, AbstractSortedOperator> progVarReplaceMap =
                extractProgramVarReplaceMap(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap, notReplaceMap,
                                        postfix, services);
    }


    private Term applyRenamingsToPrograms(Term term,
                                          Map<ProgramVariable, AbstractSortedOperator>
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
                                                   renamedJavaBlock);
            return renamedTerm;
        } else {
            return null;
        }
    }


    private Term[] renameSubs(Term term,
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
        Term resAtPostSV = (appData.pre.result == appData.post.result ?
                resAtPreSV : createTermSV(appData.post.result, schemaPrefix, services));
        Term excAtPostSV = (appData.pre.exception == appData.post.exception ?
                excAtPreSV : createTermSV(appData.post.exception, schemaPrefix, services));
        Term heapAtPostSV = (appData.pre.heap == appData.post.heap ?
                heapAtPreSV : createTermSV(appData.post.heap, schemaPrefix, services));

        // build state variable container for pre and post state
        StateVars pre =
                new StateVars(selfAtPreSV, guardAtPreSV, localVarsAtPreSVs, resAtPreSV,
                              excAtPreSV, heapAtPreSV, mbyAtPreSV, services);
        StateVars post =
                new StateVars(selfAtPostSV, guardAtPostSV, localVarsAtPostSVs, resAtPostSV,
                              excAtPostSV, heapAtPostSV, null, services);

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
        if (sort instanceof UpdateableOperator) {
            return TB.var(SchemaVariableFactory.createProgramSV(
                    VariableNamer.parseName(name.toString()), ProgramSVSort.VARIABLE, false));
        } else {
            return TB.var(SchemaVariableFactory.createTermSV(name, sort));
        }

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

    protected void addContractApplicationTaclets(Goal initiatingGoal,
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
    private static class ProgVarSchemaVarReplaceVisitor extends CreatingASTVisitor {

        private ProgramElement result = null;

        // indicates if ALL program variables are to be replace by new
        // variables with the same name
        protected boolean replaceallbynew = true;

        /**
         * stores the program variables to be replaced as keys and the new
         * program variables as values
         */
        protected Map<ProgramVariable, AbstractSortedOperator> replaceMap;

        /**
         * creates a visitor that replaces the program variables in the given
         * statement by new ones with the same name
         * @param st the statement where the prog vars are replaced
         * @param map the HashMap with the replacements
         */
        public ProgVarSchemaVarReplaceVisitor(ProgramElement st,
                                              Map<ProgramVariable, AbstractSortedOperator> map,
                                              Services services) {
        super(st, true, services);
        this.replaceMap = map;
            assert services != null;
        }

        //%%% HACK: there should be a central facility for introducing new program
        // variables; this method is also used in <code>MethodCall</code> to
        // create copies of parameter variables
        public static AbstractSortedOperator copy(ProgramVariable pv) {
        return copy(pv, "");
        }

        //%%% HACK: there should be a central facility for introducing new program
        // variables; this method is also used in <code>MethodCall</code> to
        // create copies of parameter variables
        public static AbstractSortedOperator copy(ProgramVariable pv, String postFix) {
            ProgramElementName name = pv.getProgramElementName();
            //%%% HACK: final local variables are not renamed since they can occur in an
            // anonymous class declared in their scope of visibility.
            /*      if(pv.isFinal()){
                return pv;
            }*/
            if (pv.sort() instanceof UpdateableOperator) {
                return SchemaVariableFactory.createProgramSV(
                        (VariableNamer.parseName(name.toString() + postFix, name.getCreationInfo())),
                        ProgramSVSort.VARIABLE, false);
            } else {
                return SchemaVariableFactory.createTermSV(name, pv.sort());
            }
            /*return new LocationVariable
                    (VariableNamer.parseName(name.toString() + postFix,
                            name.getCreationInfo()),
                            pv.getKeYJavaType(), pv.isFinal());*/
        }

        protected void walk(ProgramElement node) {
            if (node instanceof LocalVariableDeclaration && replaceallbynew) {
                LocalVariableDeclaration vd = (LocalVariableDeclaration)node;
                ImmutableArray<VariableSpecification> vspecs = vd.getVariableSpecifications();
                for (int i = 0; i < vspecs.size(); i++) {
                    ProgramVariable pv
                    = (ProgramVariable)
                    vspecs.get(i).getProgramVariable();
                    if (!replaceMap.containsKey(pv)) {
                        replaceMap.put(pv, copy(pv));
                    }
                }
            }
            super.walk(node);
        }

        /** starts the walker*/
        public void start() {
            stack.push(new ExtList());
            walk(root());
            ExtList el= stack.peek();
            int i=0;
            while (!(el.get(i) instanceof ProgramElement)) {
                i++;
            }
            result=(ProgramElement) stack.peek().get(i);
        }

        public ProgramElement result() {
            return result;
        }
    }
}