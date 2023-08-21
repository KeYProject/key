/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.*;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * The QueryExpand rule allows to apply contracts or to symbolically execute a query expression in
 * the logic. It replaces the query expression by a new constant and constructs a box formula in the
 * antecedent 'defining' the constant as the result of a method call. The method call is encoded
 * directly as a method call in the box modality. The query is invoked in a context equal to the
 * container type of the query method.
 *
 * @author Richard Bubel
 */
public class QueryExpand implements BuiltInRule {

    private static final Logger LOGGER = LoggerFactory.getLogger(QueryExpand.class);
    public static final QueryExpand INSTANCE = new QueryExpand();

    private static final int DEFAULT_MAP_SIZE = 200;

    private static final Name QUERY_DEF_NAME = new Name("Evaluate Query");


    /**
     * Stores a number that indicates the time when term occurred for the first time where this rule
     * was applicable. The time is the number of rules applied on this branch.
     */
    private final WeakHashMap<Term, Long> timeOfTerm = new WeakHashMap<>(DEFAULT_MAP_SIZE);


    @Nonnull
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {

        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term query = pio.subTerm();

        // new goal
        ImmutableList<Goal> newGoal = goal.split(1);
        Goal g = newGoal.head();

        Pair<Term, Term> queryEval = queryEvalTerm(services, query, null);

        // The following additional rewrite taclet increases performance
        // (sometimes significantly, e.g. by factor 10).
        RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        // The tacletName used to contain the query as String, but this lead
        // to unloadable proofs: (constant names may change between saving and
        // loading, and thus the taclet name), MU 2021
        /* + query.toString() + "_" */
        Name tacletName =
            MiscTools.toValidTacletName("replaceKnownQuery" + g.node().getUniqueTacletId());
        tb.setName(tacletName);
        tb.setDisplayName("replaceKnownQuery");
        tb.setFind(query);
        tb.setApplicationRestriction(RewriteTaclet.IN_SEQUENT_STATE);
        tb.addGoalTerm(queryEval.second);
        tb.addRuleSet(new RuleSet(new Name("concrete")));

        // move the query call directly to the succedent. Use box instead of diamond?
        g.addFormula(new SequentFormula(queryEval.first), true, true);
        g.addTaclet(tb.getTaclet(), SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        return newGoal;
    }

    /**
     * Creates an invocation of a query in a modal operator and stores the value in a new symbol.
     * This is a utility method, that may also be used by other classes.
     *
     * @param services
     * @param query The query on which the query expand rule is applied
     * @param instVars If null, then the result of the query can be stored in a constant (e.g.
     *        res=query(a)). Otherwise it is a list of logical variables that can be instantiated
     *        (using the rules allLeft, exRight) and therefore the result of the query must be
     *        stored by function that depends on instVars (e.g. forall i; res(i)=query(i)). The list
     *        may be empty even if it not null.
     * @return The formula (!{U}<result=query();>result=res_query) & query()=res_query
     * @author Richard Bubel
     * @author gladisch
     */
    public Pair<Term, Term> queryEvalTerm(Services services, Term query, LogicVariable[] instVars) {

        final IProgramMethod method = (IProgramMethod) query.op();

        final ImmutableArray<ProgramVariable> args =
            getRegisteredArgumentVariables(method.getParameters(), services);

        final TermBuilder tb = services.getTermBuilder();

        // Names for additional symbols

        final String calleeName = tb.newName("callee");
        final String progResultName = tb.newName("queryResult");
        final String logicResultName = tb.newName("res_" + method.getName());
        // For declaring the symbol that stores the result in a logical term a trick is done.
        // The new symbolc is introduced as a logical variable that is later skolemized by the
        // ex_left rule.
        // LogicVariable logicResultQV = new LogicVariable(new
        // Name("res_"+method.getName()),query.sort())

        KeYJavaType calleeType = services.getJavaInfo().getKeYJavaType(query.arity() == 1 ? // static
                                                                                            // query
                query.sort() : query.sub(1).sort());
        KeYJavaType progResultType = method.getReturnType();


        final ProgramVariable callee;
        final int offset;
        if (method.isStatic()) {
            callee = null;
            offset = 0;
        } else {
            callee = new LocationVariable(new ProgramElementName(calleeName), calleeType);
            offset = 1;
        }

        final ProgramVariable result =
            new LocationVariable(new ProgramElementName(progResultName), progResultType);


        final MethodReference mr =
            new MethodReference(args, method.getProgramElementName(), callee);

        final Function placeHolderResult;
        final Term placeHolderResultTrm;

        if (instVars == null || instVars.length == 0) {
            placeHolderResult = new Function(new Name(logicResultName), query.sort());
            placeHolderResultTrm = tb.func(placeHolderResult);
        } else {
            // If the query expansion depends on logical variables, then store the result in a
            // function
            // that depends on the logical variables.
            Term[] lvTrms = new Term[instVars.length];
            Sort[] lvSorts = new Sort[instVars.length];
            for (int i = 0; i < instVars.length; i++) {
                lvTrms[i] = tb.var(instVars[i]);
                lvSorts[i] = instVars[i].sort();
            }
            ImmutableArray<Sort> imArrlvSorts = new ImmutableArray<>(lvSorts);
            placeHolderResult = new Function(new Name(logicResultName), query.sort(), imArrlvSorts);
            placeHolderResultTrm = tb.func(placeHolderResult, lvTrms, null); // I'm not sure about
                                                                             // the third parameter!
        }

        services.getNamespaces().functions().addSafely(placeHolderResult);

        // construct method call {heap:=h || p1:arg1 || ... || pn:=argn}
        // \[ res = o.m(p1,..,pn); \] (c = res)

        ArrayList<ProgramElement> stmnt = new ArrayList<>();

        stmnt.add(KeYJavaASTFactory.declare(result, progResultType));

        final CopyAssignment assignment = new CopyAssignment(result, mr);

        stmnt.add(assignment);

        StatementBlock s = new StatementBlock(stmnt.toArray(new Statement[0]));


        final MethodFrame mf = new MethodFrame(null,
            new ExecutionContext(new TypeRef(method.getContainerType()), method, null),
            // new StatementBlock(assignment)
            s);
        final JavaBlock jb = JavaBlock.createJavaBlock(new StatementBlock(mf));

        // Not sure if box or diamond should be used.
        final Term methodCall = tb.dia(jb, tb.not(tb.equals(tb.var(result), placeHolderResultTrm)));

        Term update =
            tb.elementary(services.getTypeConverter().getHeapLDT().getHeap(), query.sub(0));
        if (callee != null) {
            update = tb.parallel(tb.elementary(tb.var(callee), query.sub(1)), update);
        }

        final Term[] argUpdates = new Term[args.size()];
        for (int i = 0; i < args.size(); i++) {
            argUpdates[i] = tb.elementary(tb.var(args.get(i)), query.sub(offset + 1 + i));
        }

        update = tb.parallel(update, tb.parallel(argUpdates));

        Term topLevel = tb.not(tb.apply(update, methodCall, null));


        // The following additional equation increases performance (sometimes significantly, e.g. by
        // factor 10).
        // CS: It is even more efficien to introduce a rewrite taclet instead
        // of an equation. Therefore return the placeHolderResultTrm such that
        // the caller can decide whether to introduce an equation or taclet.
        // topLevel = tb.and(topLevel, tb.equals(query,placeHolderResultTrm))
        // topLevel = tb.ex(logicResultQV, topLevel); //Alternative way to declare the symbol

        return new Pair<>(topLevel, placeHolderResultTrm);
    }


    private ImmutableArray<ProgramVariable> getRegisteredArgumentVariables(
            ImmutableArray<ParameterDeclaration> paramDecls, TermServices services) {

        final Namespace<IProgramVariable> progvarsNS = services.getNamespaces().programVariables();
        final ProgramVariable[] args = new ProgramVariable[paramDecls.size()];
        int i = 0;
        for (final ParameterDeclaration pdecl : paramDecls) {
            final String baseName = pdecl.getVariableSpecification().getName();
            final String newName = services.getTermBuilder().newName(baseName);
            final ProgramElementName argVarName = new ProgramElementName(newName);
            args[i] = new LocationVariable(argVarName,
                pdecl.getVariableSpecification().getProgramVariable().getKeYJavaType());
            progvarsNS.addSafely(args[i]);
            i++;
        }

        return new ImmutableArray<>(args);
    }


    /**
     * Apply "evaluate query" to the queries that occur in <code>term</code>. The query
     * evaluations/expansions are inserted into a copy of <code>term</code> that is returned.
     *
     * @param services
     * @param term A formula that potentially contains queries that should be evaluated/expanded.
     * @param positiveContext Set false iff the <code>term</code> is in a logically negated context
     *        wrt. to the succedent.
     * @param allowExpandBelowInstQuantifier TODO
     * @return A modified version of the <code>term</code> with inserted "query evalutions".
     * @author gladisch
     */
    public Term evaluateQueries(Services services, Term term, boolean positiveContext,
            boolean allowExpandBelowInstQuantifier) {
        final int depth = term.depth();
        List<QueryEvalPos> qeps = new ArrayList<>();
        int[] path = new int[depth];
        final ImmutableSLList<QuantifiableVariable> instVars;
        if (allowExpandBelowInstQuantifier) {
            instVars = ImmutableSLList.nil();
        } else {
            instVars = null;
        }
        findQueriesAndEvaluationPositions(term, 0, path, instVars, positiveContext, 0,
            positiveContext, qeps);
        removeRedundant(qeps);
        // sorting is important in order to ensure that the original term is modified in a
        // depth-first order.
        Collections.sort(qeps);
        final TermBuilder tb = services.getTermBuilder();

        for (QueryEvalPos qep : qeps) {
            Pair<Term, Term> queryExp =
                QueryExpand.INSTANCE.queryEvalTerm(services, qep.query, qep.instVars);
            Term queryExpTerm = tb.and(queryExp.first, tb.equals(qep.query, queryExp.second));
            final Term termToInsert;
            if (qep.positivePosition) {
                termToInsert = tb.imp(queryExpTerm, qep.getTermOnPath(term));
            } else {
                termToInsert = tb.and(queryExpTerm, qep.getTermOnPath(term));
            }
            // Attention, when the term is modified, then the paths in the term have changed.
            // Perform the changes in a depth-first order.
            term = replace(term, termToInsert, qep.pathInTerm, 1, services);
        }
        return term;
    }


    /**
     * Find queries in t and suitable positions where to insert their evaluations in t. This method
     * is called by the method <code>evaluateQueries<\code>.
     *
     * @param t The term where to search for queries and query evaluation positions.
     * @param level The current recursion level of this method call.
     * @param pathInTerm List of integers describing the current path in the syntax tree (of the
     *        term at level 0).
     * @param instVars If null, then query evaluation below instantiable quantifiers (i.e.
     *        non-Skolemizable quantifiers) is suppressed. If not null, then this list collects the
     *        logical variables of instantiable quantifers that the query evaluation depends on.
     *        This is to needed to create e.g. (forall i; query(i)=res(i)) instead of (forall
     *        i;query(i)=res); the latter is unsound.
     * @param curPosIsPositive True iff the current position in the formula we are in is a logically
     *        positive context (when considering polarity wrt. logical negation).
     * @param qepLevel The top-most level on the current path where the query evaluation could be
     *        inserted. Its either top-level (0) or below a quantifier.
     * @param qepIsPositive True iff the logical context at position qepLevel is positive (i.e., not
     *        negated, or negations have cancelled out).
     * @param qeps The resulting collection of query evaluation positions.
     * @author gladisch
     */
    @SuppressWarnings("unchecked")
    private void findQueriesAndEvaluationPositions(Term t, int level, int[] pathInTerm,
            ImmutableList<QuantifiableVariable> instVars, boolean curPosIsPositive, int qepLevel,
            boolean qepIsPositive, List<QueryEvalPos> qeps) {
        if (t == null) {
            return;
        }
        final Operator op = t.op();
        final int nextLevel = level + 1;
        if (op instanceof IProgramMethod && !((IProgramMethod) op).isModel()) { // Query found
            QueryEvalPos qep = new QueryEvalPos(t, Arrays.copyOf(pathInTerm, qepLevel + 1),
                instVars, qepIsPositive);
            qeps.add(qep);
        } else if (op == Junctor.AND || op == Junctor.OR) {
            pathInTerm[nextLevel] = 0;
            findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                curPosIsPositive, qepLevel, qepIsPositive, qeps);
            pathInTerm[nextLevel] = 1;
            findQueriesAndEvaluationPositions(t.sub(1), nextLevel, pathInTerm, instVars,
                curPosIsPositive, qepLevel, qepIsPositive, qeps);
        } else if (op == Junctor.IMP) {
            pathInTerm[nextLevel] = 0;
            findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                !curPosIsPositive, qepLevel, qepIsPositive, qeps);
            pathInTerm[nextLevel] = 1;
            findQueriesAndEvaluationPositions(t.sub(1), nextLevel, pathInTerm, instVars,
                curPosIsPositive, qepLevel, qepIsPositive, qeps);
        } else if (op == Junctor.NOT) {
            pathInTerm[nextLevel] = 0;
            findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                !curPosIsPositive, qepLevel, qepIsPositive, qeps);
        } else if (op == Equality.EQV) {
            // Each subformula of "<->" is in both, positive and negative scope. Query expansion
            // below it would be unsound.
            // Alternatively "<->" could be converted into "->" and "<-"
        } else if (t.javaBlock() != JavaBlock.EMPTY_JAVABLOCK) { // do not descend below java
                                                                 // blocks.
        } else if (op == Quantifier.ALL) {
            if (curPosIsPositive) { // Quantifier that will be Skolemized
                // This is a potential query evaluation position.
                pathInTerm[nextLevel] = 0;
                findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                    curPosIsPositive, nextLevel, curPosIsPositive, qeps);
            } else { // Quantifier that will be instantiated. Warning: this may explode!
                if (instVars != null) {
                    pathInTerm[nextLevel] = 0;
                    assert t.boundVars().get(0) instanceof LogicVariable;
                    instVars = instVars.append(t.boundVars());
                    findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                        curPosIsPositive, nextLevel, curPosIsPositive, qeps);
                }
            }
        } else if (op == Quantifier.EX) {
            if (curPosIsPositive) { // Quantifier that will be instantiated. Warning: this may
                                    // explode!
                if (instVars != null) {
                    pathInTerm[nextLevel] = 0;
                    assert t.boundVars().get(0) instanceof LogicVariable;
                    instVars = instVars.append(t.boundVars());
                    findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                        curPosIsPositive, nextLevel, curPosIsPositive, qeps);
                }
            } else { // Quantifier that will be Skolemized
                // This is a potential query evaluation position.
                pathInTerm[nextLevel] = 0;
                findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars,
                    curPosIsPositive, nextLevel, curPosIsPositive, qeps);
            }
        } else if (t.sort() == Sort.FORMULA) {
            ArrayList<Term> queries = collectQueries(t);
            for (Term query : queries) {
                QueryEvalPos qep = new QueryEvalPos(query, Arrays.copyOf(pathInTerm, qepLevel + 1),
                    instVars, qepIsPositive);
                qeps.add(qep);
            }
        }
    }


    private ArrayList<Term> collectQueries(Term t) {
        ArrayList<Term> queries = new ArrayList<>();
        collectQueriesRecursively(t, queries);
        return queries;
    }


    /**
     * Utility method called by <code>collectQueriesRecursively</code>
     */
    private void collectQueriesRecursively(Term t, List<Term> result) {
        if (t.javaBlock() != JavaBlock.EMPTY_JAVABLOCK) {
            return;
        }
        // What about checking if an update is encountered?
        if (t.op() instanceof IProgramMethod && !((IProgramMethod) t.op()).isModel()) {
            // Query found
            result.add(t);
        } else {
            for (int i = 0; i < t.arity(); i++) {
                collectQueriesRecursively(t.sub(i), result);
            }
        }
    }


    /**
     * Tries to remove redundant query evaluations/expansions.
     */
    private void removeRedundant(List<QueryEvalPos> qeps) {
        int size = qeps.size();
        for (int i = 0; i < size; i++) {
            QueryEvalPos cur = qeps.get(i);
            for (int k = 0; k < size; k++) {
                QueryEvalPos other = qeps.get(k);
                if (i != k && cur.subsumes(other)) {
                    qeps.remove(k);
                    size--;
                }
            }
        }
    }


    /**
     * Query evaluation position. Describes where to insert a query evaluation/expansion (see
     * <code>QueryExpand</code>) in a formula.
     *
     * @author gladisch
     */
    private static class QueryEvalPos implements Comparable<QueryEvalPos> {

        /**
         * The query that is subject to query evaluation/expansion. The query itself is not modified
         * but a formula is added at a position described by the other fields.
         */
        public final Term query;
        /**
         * Positive or negative position wrt. logical negation.
         */
        public final boolean positivePosition;
        /**
         * Path in the syntax tree of the term where the query evaluation/expansion should be
         * inserted. The first element has no meaning and should be null. The path starts with the
         * second element.
         */
        public final int[] pathInTerm;

        public final LogicVariable[] instVars;

        public QueryEvalPos(Term query, int[] path, ImmutableList<QuantifiableVariable> iVars,
                boolean isPositive) {
            this.query = query;
            pathInTerm = path;
            positivePosition = isPositive;
            if (iVars != null) {
                instVars = new LogicVariable[iVars.size()];
                iVars.toArray(instVars);
            } else {
                instVars = new LogicVariable[0];
            }
        }


        public String toString() {
            StringBuilder pathstr = new StringBuilder("[");
            for (int in : pathInTerm) {
                pathstr.append(in).append(", ");
            }
            pathstr.append("]");
            return "QueryEvalPos of " + (query != null ? query.toString() : "NOQUERY") + " in "
                + (positivePosition ? "positive" : "negative") + " position "
                + (instVars.length > 0 ? "  instVar:" + instVars[0] + " " : "") + " insertPath:"
                + pathstr;
        }

        public Term getTermOnPath(Term root) {
            Term result = root;
            for (int i = 1 /* skip the first */; i < pathInTerm.length; i++) {
                result = result.sub(pathInTerm[i]);
            }
            return result;
        }


        public boolean subsumes(QueryEvalPos other) {
            if (!query.equals(other.query) || pathInTerm.length > other.pathInTerm.length
                    || !Arrays.deepEquals(instVars, other.instVars)) {
                return false;
            }
            // query.equals(other.query) && pathInTerm.size()<=other.pathInTerm.size()
            for (int i = 0; i < pathInTerm.length; i++) {
                if (pathInTerm[i] != other.pathInTerm[i]) {
                    return false;
                }
            }
            return true;
        }

        /**
         * For sorting. Longer paths come first in order to apply modifications to the target term
         * in a depth-first order.
         */
        @Override
        public int compareTo(QueryEvalPos other) {
            final int otherSize = other.pathInTerm.length;
            final int thisSize = pathInTerm.length;
            return (Integer.compare(otherSize, thisSize));
        }
    }


    /**
     * Replaces in a term.
     *
     * @param term
     * @param with
     * @param it iterator with argument positions. This is the path in the syntax tree of term.
     * @param services TODO
     * @return Resulting term after replacement.
     * @note Was originally implemented in QueryExpand.java.
     */
    protected Term replace(Term term, Term with, int[] it, int idx, TermServices services) {
        if (!(idx < it.length)) {
            return with;
        }

        final int arity = term.arity();
        final Term[] newSubTerms = new Term[arity];
        boolean changedSubTerm = false;
        int next = it[idx++];
        for (int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            if (i == next) {
                newSubTerms[i] = replace(subTerm, with, it, idx, services);
                if (newSubTerms[i] != subTerm) {
                    changedSubTerm = true;
                }
            } else {
                newSubTerms[i] = subTerm;
            }

        }

        final ImmutableArray<QuantifiableVariable> newBoundVars = term.boundVars();

        final Term result;
        if (changedSubTerm) {
            result = services.getTermFactory().createTerm(term.op(), newSubTerms, newBoundVars,
                term.javaBlock());
        } else {
            result = term;
        }

        return result;
    }


    @Override
    public Name name() {
        return QUERY_DEF_NAME;
    }

    @Override
    public String displayName() {
        return QUERY_DEF_NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }

    /**
     * Important the correctness of the implementation of this rule relies on the following
     * side-conditions:
     * <ul>
     * <li>the query term has no free variables</li>
     * <li>the query term does not occur below an update or a modality</li>
     * </ul>
     * If you want to change this you need to adapt the application logic by adding preceding
     * updates in front of the new added formula and/or to take care of free variables when
     * introducing the skolemfunction symbol and when replacing the query term by the skolem
     * function.
     *
     * The method is equipped with a side-effect that stores the age of the term. This information
     * is useful for <code>QueryExpandCost</cost>.
     */
    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio != null && pio.subTerm().op() instanceof IProgramMethod
                && pio.subTerm().freeVars().isEmpty()) {
            final Term pmTerm = pio.subTerm();
            IProgramMethod pm = (IProgramMethod) pmTerm.op();
            if (pm.isModel()) {
                return false;
            }
            // abort if inside of transformer
            if (Transformer.inTransformer(pio)) {
                return false;
            }
            final Sort nullSort = goal.proof().getJavaInfo().nullSort();
            if (pm.isStatic()
                    || (pmTerm.sub(1).sort().extendsTrans(goal.proof().getJavaInfo().objectSort())
                            && !pmTerm.sub(1).sort().extendsTrans(nullSort))) {
                PIOPathIterator it = pio.iterator();
                while (it.next() != -1) {
                    Term focus = it.getSubTerm();
                    if (focus.op() instanceof UpdateApplication || focus.op() instanceof Modality) {
                        return false;
                    }
                }
                storeTimeOfQuery(pio.subTerm(), goal);
                return true;
            }
        }
        return false;
    }

    private void storeTimeOfQuery(Term query, Goal goal) {
        if (timeOfTerm.get(query) == null) {
            timeOfTerm.put(query, goal.getTime());
        }
    }

    public Long getTimeOfQuery(Term t) {
        if (t == null || !(t.op() instanceof IProgramMethod)) {
            LOGGER.warn(
                "QueryExpand::getAgeOfQuery(t). The term is expected to be a query but it is: {}",
                (t != null ? t : "null"));
            return null;
        }
        return timeOfTerm.get(t);

    }

    @Override
    public DefaultBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }
}
