/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.mergerule;

import java.io.StringReader;
import java.util.*;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.collection.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class encapsulates static methods used in the MergeRule implementation. The methods are
 * organized into different sections (see comments):
 * <p>
 *
 * <ol>
 * <li>SIMPLE AUXILIARIES</li>
 * <li>GENERAL LOGIC
 * <ol>
 * <li>Syntax</li>
 * <li>Provability</li>
 * <li>Simplification</li>
 * <li>Calculus</li>
 * </ol>
 * </li>
 * <li>MERGE RELATED</li>
 * <li>PRIVATE</li>
 * </ol>
 *
 * Feel free to make private methods publicly visible if you need them.
 *
 * @author Dominic Scheurer
 */
public class MergeRuleUtils {
    private static final Logger LOGGER = LoggerFactory.getLogger(MergeRuleUtils.class);

    // ////////////////////////////////////////////////
    // ///////////// SIMPLE AUXILIARIES ///////////////
    // ////////////////////////////////////////////////

    /**
     * Wraps the given object s.th. if it is null, a None value is returned, and a Some value
     * wrapping the object is returned otherwise.
     *
     * @param obj The object to wrap.
     * @return None iff obj is null, Some(obj) otherwise.
     */
    public static <T> Optional<T> wrapOption(T obj) {
        if (obj == null) {
            return Optional.empty();
        } else {
            return Optional.of(obj);
        }
    }

    /**
     * For Strings "xxx_i", this method returns "xxx". For Strings without the underscore, the
     * original String is returned.
     *
     * @param name Name to remove the index from.
     * @return The name without the index, if any.
     */
    public static String stripIndex(String name) {
        int underscoreOccurrence = name.indexOf('_');
        if (underscoreOccurrence > -1) {
            return name.substring(0, underscoreOccurrence);
        } else {
            return name;
        }
    }

    /**
     * Power function for integers.
     *
     * @param a The base.
     * @param b The exponent.
     * @return a^b.
     */
    public static int intPow(int a, int b) {
        return (int) Math.round(Math.pow(a, b));
    }

    /**
     * Creates an {@link ArrayList} containing exactly the given element.
     *
     * @param elem Element that is contained in the returned list.
     * @return An {@link ArrayList} containing exactly the given element.
     */
    public static <T> ArrayList<T> singletonArrayList(T elem) {
        ArrayList<T> result = new ArrayList<>();
        result.add(elem);
        return result;
    }

    // /////////////////////////////////////////////////
    // //////////////// GENERAL LOGIC //////////////////
    // //////////////// (Syntax) //////////////////
    // /////////////////////////////////////////////////

    /**
     * Translates a String into a formula or to null if not applicable.
     *
     * @param services The services object.
     * @param toTranslate The formula to be translated.
     * @return The formula represented by the input or null if not applicable.
     */
    public static Term translateToFormula(final Services services, final String toTranslate) {
        try {
            @Nonnull
            Term result = new KeyIO(services).parseExpression(toTranslate);
            return result.sort() == Sort.FORMULA ? result : null;
        } catch (Throwable e) {
            return null;
        }
    }

    /**
     * @param u The update (in normal form) to extract program locations from.
     * @return All program locations (left sides) in the given update.
     */
    public static ImmutableSet<LocationVariable> getUpdateLeftSideLocations(Term u) {
        if (u.op() instanceof ElementaryUpdate) {

            ImmutableSet<LocationVariable> result = DefaultImmutableSet.nil();
            result = result.add((LocationVariable) ((ElementaryUpdate) u.op()).lhs());
            return result;

        } else if (u.op() instanceof UpdateJunctor) {

            ImmutableSet<LocationVariable> result = DefaultImmutableSet.nil();
            for (Term sub : u.subs()) {
                result = result.union(getUpdateLeftSideLocations(sub));
            }
            return result;

        } else {

            throw new IllegalStateException("Update should be in normal form!");

        }
    }

    /**
     * Returns all elementary updates of a parallel update.
     *
     * @param u Parallel update to get elementary updates from.
     * @return Elementary updates of the supplied parallel update.
     */
    public static LinkedList<Term> getElementaryUpdates(Term u) {
        LinkedList<Term> result = new LinkedList<>();

        if (u.op() instanceof ElementaryUpdate) {
            result.add(u);
        } else if (u.op() instanceof UpdateJunctor) {
            for (Term sub : u.subs()) {
                result.addAll(getElementaryUpdates(sub));
            }
        } else {
            throw new IllegalArgumentException("Expected an update!");
        }

        return result;
    }

    /**
     * Returns all program variables in the given term.
     *
     * @param term The term to extract program variables from.
     * @return All program variables of the given term.
     */
    public static ImmutableSet<LocationVariable> getLocationVariables(Term term,
            Services services) {
        ImmutableSet<LocationVariable> result = DefaultImmutableSet.nil();

        if (term.op() instanceof LocationVariable) {
            result = result.add((LocationVariable) term.op());
        } else {
            if (!term.javaBlock().isEmpty()) {
                result = result.union(getProgramLocations(term, services));
            }

            for (Term sub : term.subs()) {
                result = result.union(getLocationVariables(sub, services));
            }
        }

        return result;
    }

    /**
     * Returns all program variables in the given sequent.
     *
     * @param sequent The sequent to extract program variables from.
     * @return All program variables of the given sequent.
     */
    public static HashSet<LocationVariable> getLocationVariablesHashSet(Sequent sequent,
            Services services) {
        HashSet<LocationVariable> result = new HashSet<>();

        for (SequentFormula f : sequent) {
            result.addAll(getLocationVariablesHashSet(f.formula(), services));
        }

        return result;
    }

    /**
     * Returns all program variables in the given term.
     *
     * @param term The term to extract program variables from.
     * @return All program variables of the given term.
     */
    public static HashSet<LocationVariable> getLocationVariablesHashSet(Term term,
            Services services) {
        HashSet<LocationVariable> result = new HashSet<>();

        if (term.op() instanceof LocationVariable) {
            result.add((LocationVariable) term.op());
        } else {
            if (!term.javaBlock().isEmpty()) {
                result.addAll(getProgramLocationsHashSet(term, services));
            }

            for (Term sub : term.subs()) {
                result.addAll(getLocationVariablesHashSet(sub, services));
            }
        }

        return result;
    }

    /**
     * Returns all Skolem constants in the given term.
     *
     * @param term The term to extract Skolem constants from.
     * @return All SkolemConstants of the given term.
     */
    public static HashSet<Function> getSkolemConstants(Term term) {
        HashSet<Function> result = new HashSet<>();

        if (term.op() instanceof Function && ((Function) term.op()).isSkolemConstant()) {
            result.add((Function) term.op());
        } else {
            for (Term sub : term.subs()) {
                result.addAll(getSkolemConstants(sub));
            }
        }

        return result;
    }

    /**
     * Returns the right side for a given location variable in an update (in normal form).
     *
     * @param update Update term to search.
     * @param leftSide Left side to find the right side for.
     * @return The right side in the update for the given left side. Returns a None value if the
     *         right side could not be determined.
     */
    public static Optional<Term> getUpdateRightSideForSafe(Term update, LocationVariable leftSide) {
        return wrapOption(getUpdateRightSideFor(update, leftSide));
    }

    /**
     * Returns the right side for a given location variable in an update (in normal form).
     *
     * @param update Update term to search.
     * @param leftSide Left side to find the right side for.
     * @return The right side in the update for the given left side, or null if the right side could
     *         not be determined.
     */
    public static Term getUpdateRightSideFor(Term update, LocationVariable leftSide) {
        if (update.op() instanceof ElementaryUpdate
                && ((ElementaryUpdate) update.op()).lhs().equals(leftSide)) {

            return update.sub(0);

        } else if (update.op() instanceof UpdateJunctor
                && update.op().equals(UpdateJunctor.PARALLEL_UPDATE)) {

            for (Term sub : update.subs()) {
                Term rightSide = getUpdateRightSideFor(sub, leftSide);
                if (rightSide != null) {
                    return rightSide;
                }
            }

            return null;

        } else {
            return null;
        }
    }

    /**
     * Counts the atoms in a formula.
     *
     * @param term Formula to count atoms for.
     * @return Number of atoms in the formula
     * @throws IllegalArgumentException if the supplied term is not a formula
     */
    public static int countAtoms(Term term) {
        if (term.sort().equals(Sort.FORMULA)) {
            if (term.op() instanceof Junctor) {
                int result = 0;
                for (Term sub : term.subs()) {
                    result += countAtoms(sub);
                }
                return result;
            } else {
                return 1;
            }
        } else {
            throw new IllegalArgumentException("Can only compute atoms for formulae");
        }
    }

    /**
     * Counts the disjunctions in a formula.
     *
     * @param term Formula to count disjunctions for.
     * @param negated Set to true iff the current subformula is in the scope of a negation; in this
     *        case, "and" junctors have the role of "or" junctors considering the disjunctive
     *        complexity.
     * @return Number of disjunctions in the formula
     * @throws IllegalArgumentException if the supplied term is not a formula
     */
    public static int countDisjunctions(Term term, boolean negated) {
        if (term.sort().equals(Sort.FORMULA)) {
            if (term.op() instanceof Junctor) {
                int result = 0;

                if (!negated && term.op().equals(Junctor.OR)
                        || !negated && term.op().equals(Junctor.IMP)
                        || negated && term.op().equals(Junctor.AND)) {
                    result++;
                }

                if (term.op().equals(Junctor.NOT)) {
                    negated = !negated;
                }

                for (Term sub : term.subs()) {
                    result += countDisjunctions(sub, negated);
                }

                return result;
            } else {
                return 0;
            }
        } else {
            throw new IllegalArgumentException("Can only compute atoms for formulae");
        }
    }

    /**
     * Computes and registers a new Skolem constant with the given prefix in its name of the given
     * sort.
     *
     * @param prefix Prefix for the name of the constant.
     * @param sort Sort of the constant.
     * @param services The services object.
     * @return A new Skolem constant of the given sort with the given prefix in its name.
     */
    public static Function getNewSkolemConstantForPrefix(String prefix, Sort sort,
            Services services) {
        Function result = null;
        String newName = "";

        do {
            newName = services.getTermBuilder().newName(prefix);
            result = new Function(new Name(newName), sort, true);
            services.getNamespaces().functions().add(result);
        } while (newName.equals(prefix));

        return result;
    }

    /**
     * Computes and registers a fresh variable with the given prefix in its name of the given sort.
     *
     * @param prefix Prefix for the name of the variable.
     * @param sort Sort of the variable.
     * @param services The services object.
     * @return A fresh variable of the given sort with the given prefix in its name.
     */
    public static LogicVariable getFreshVariableForPrefix(String prefix, Sort sort,
            Services services) {
        LogicVariable result = null;
        String newName = "";

        do {
            newName = services.getTermBuilder().newName(prefix);
            result = new LogicVariable(new Name(newName), sort);
            services.getNamespaces().variables().add(result);
        } while (newName.equals(prefix));

        return result;
    }

    /**
     * Computes and registers a fresh location variable with the given prefix in its name of the
     * given sort.
     *
     * @param prefix Prefix for the name of the variable.
     * @param sort Sort of the variable.
     * @param services The services object.
     * @return A fresh location variable of the given sort with the given prefix in its name.
     */
    public static LocationVariable getFreshLocVariableForPrefix(String prefix, Sort sort,
            Services services) {
        LocationVariable result = null;
        String newName = "";

        do {
            newName = services.getTermBuilder().newName(prefix);
            result = new LocationVariable(//
                new ProgramElementName(newName), sort);
            Namespace<IProgramVariable> variables = //
                services.getNamespaces().programVariables();
            variables.add(result);
        } while (newName.equals(prefix));

        return result;
    }

    /**
     * Substitutes all constants in the given term by fresh variables. Multiple occurrences of a
     * constant are substituted by the same variable.
     *
     * @param term Term in which to substitute constants by variables.
     * @param replMap Map from constants to variables in order to remember substitutions of one
     *        constant.
     * @return A term equal to the input, but with constants substituted by fresh variables.
     */
    public static Term substConstantsByFreshVars(Term term,
            HashMap<Function, LogicVariable> replMap, Services services) {
        return substConstantsByFreshVars(term, null, replMap, services);
    }

    /**
     * Substitutes all constants in the given term that are contained in the set restrictTo by fresh
     * variables. If restrictTo is null, then all constants in the term are replaced. Multiple
     * occurrences of a constant are substituted by the same variable.
     *
     * @param term Term in which to substitute constants by variables.
     * @param restrictTo Set of constants to replace. If null, all constants are replaced.
     * @param replMap Map from constants to variables in order to remember substitutions of one
     *        constant.
     * @return A term equal to the input, but with constants substituted by fresh variables.
     */
    public static Term substConstantsByFreshVars(Term term, HashSet<Function> restrictTo,
            HashMap<Function, LogicVariable> replMap, Services services) {
        TermBuilder tb = services.getTermBuilder();

        if (term.op() instanceof Function && ((Function) term.op()).isSkolemConstant()
                && (restrictTo == null || restrictTo.contains(term.op()))) {

            Function constant = (Function) term.op();

            if (!replMap.containsKey(constant)) {
                LogicVariable freshVariable = getFreshVariableForPrefix(
                    stripIndex(constant.toString()), constant.sort(), services);
                replMap.put(constant, freshVariable);
            }

            return tb.var(replMap.get(constant));

        } else {

            LinkedList<Term> transfSubs = new LinkedList<>();
            for (Term sub : term.subs()) {
                transfSubs.add(substConstantsByFreshVars(sub, restrictTo, replMap, services));
            }

            return services.getTermFactory().createTerm(term.op(),
                new ImmutableArray<>(transfSubs), term.boundVars(), term.javaBlock(),
                term.getLabels());

        }
    }

    /**
     * Existentially closes all logical and location variables in the given term.
     *
     * @param term Term to existentially close.
     * @param services The services object.
     * @return A new term which is equivalent to the existential closure of the argument term.
     */
    public static Term exClosure(final Term term, final Services services) {
        TermBuilder tb = services.getTermBuilder();
        Pair<Term, ImmutableSet<QuantifiableVariable>> anonymized =
            anonymizeProgramVariables(term, services);

        return tb.ex(anonymized.second, anonymized.first);
    }

    /**
     * Universally closes all logical and location variables in the given term.
     *
     * @param term Term to universally close.
     * @param services The services object.
     * @return A new term which is equivalent to the universal closure of the argument term.
     */
    public static Term allClosure(final Term term, final Services services) {
        TermBuilder tb = services.getTermBuilder();
        Pair<Term, ImmutableSet<QuantifiableVariable>> anonymized =
            anonymizeProgramVariables(term, services);

        return tb.all(anonymized.second, anonymized.first);
    }

    /**
     * Checks if an update is of the form { x := v || ... || z := q}.
     *
     * @param u Update to check.
     * @return true iff u is in normal form.
     */
    public static boolean isUpdateNormalForm(Term u) {
        if (u.op() instanceof ElementaryUpdate) {
            return true;
        } else if (u.op() instanceof UpdateJunctor) {
            boolean result = true;
            for (Term sub : u.subs()) {
                result = result && isUpdateNormalForm(sub);
            }
            return result;
        } else {
            return false;
        }
    }

    /**
     * Dissects a conjunction into its conjunctive elements.
     *
     * @param term Conjunctive formula to dissect (may be a conjunction of one element, i.e. no
     *        "real" conjunction). In this case, the resulting list will contain exactly the
     *        supplied formula.
     * @return The conjunctive elements of the supplied formula.
     */
    public static ArrayList<Term> getConjunctiveElementsFor(final Term term) {
        ArrayList<Term> result = new ArrayList<>();

        if (term.op().equals(Junctor.AND)) {
            result.addAll(getConjunctiveElementsFor(term.sub(0)));
            result.addAll(getConjunctiveElementsFor(term.sub(1)));
        } else {
            result.add(term);
        }

        return result;
    }

    /**
     * Find a location variable for the given one that is unique for the branch corresponding to the
     * given goal, but not necessarily globally unique. The variable with the first branch-unique
     * name w.r.t. a numeric index is returned.
     *
     * @param var Variable to get a branch-unique correspondent for.
     * @param startLeaf The leaf of the branch.
     * @return The first indexed PV that is unique w.r.t. the given branch, but not with the global
     *         variable registry.
     */
    public static LocationVariable getBranchUniqueLocVar(LocationVariable var, Node startLeaf) {

        Services services = startLeaf.proof().getServices();

        // Find the node where the variable was introduced
        Node intrNode = getIntroducingNodeforLocVar(var, startLeaf);

        String base = stripIndex(var.name().toString());

        int newCounter = 0;
        String branchUniqueName = base;
        Iterable<IProgramVariable> progVars = intrNode.getLocalProgVars();
        while (!isUniqueInGlobals(branchUniqueName, progVars)
                || (lookupVarInNS(branchUniqueName, services) != null
                        && !lookupVarInNS(branchUniqueName, services).sort().equals(var.sort()))) {
            newCounter += 1;
            branchUniqueName = base + "_" + newCounter;
        }

        LocationVariable branchUniqueVar = lookupVarInNS(branchUniqueName, services);

        return branchUniqueVar == null ? var : branchUniqueVar;
    }

    /**
     * Finds the node, from the given leaf on, where the variable was introduced.
     *
     * @param var Variable to find introducing node for.
     * @param node Leaf to start from.
     * @return The node where the variable was introduced.
     */
    public static Node getIntroducingNodeforLocVar(LocationVariable var, Node node) {

        while (!node.root() && node.getLocalProgVars().contains(var)) {
            node = node.parent();
        }

        return node;

    }

    /**
     * Returns the first Java block in the given term that can be found by recursive search, or the
     * empty block if there is no non-empty Java block in the term.
     *
     * @param term The term to extract Java blocks for.
     * @return The first Java block in the given term or the empty block if there is no non-empty
     *         Java block.
     */
    public static JavaBlock getJavaBlockRecursive(Term term) {
        if (!term.containsJavaBlockRecursive()) {
            return JavaBlock.EMPTY_JAVABLOCK;
        }

        if (term.subs().size() == 0 || !term.javaBlock().isEmpty()) {
            return term.javaBlock();
        } else {
            for (Term sub : term.subs()) {
                JavaBlock subJavaBlock = getJavaBlockRecursive(sub);
                if (!subJavaBlock.isEmpty()) {
                    return subJavaBlock;
                }
            }
            return JavaBlock.EMPTY_JAVABLOCK;
        }
    }

    // /////////////////////////////////////////////////
    // //////////////// GENERAL LOGIC //////////////////
    // //////////////// (Provability) //////////////////
    // /////////////////////////////////////////////////

    /**
     * Tries to prove the given formula without splitting and returns whether the prove could be
     * closed.
     *
     * @param toProve Formula to prove.
     * @param services The services object.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return True iff the given formula has been successfully proven.
     */
    public static boolean isProvable(Term toProve, Services services, int timeout) {
        return isProvable(toProve, services, false, timeout);
    }

    /**
     * Tries to prove the given formula with splitting and returns whether the prove could be
     * closed.
     *
     * @param toProve Formula to prove.
     * @param services The services object.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return True iff the given formula has been successfully proven.
     */
    public static boolean isProvableWithSplitting(Term toProve, Services services, int timeout) {
        return isProvable(toProve, services, true, timeout);
    }

    /**
     * Tries to prove the given formula without splitting and returns whether the prove could be
     * closed.
     *
     * @param toProve Sequent to prove.
     * @param services The services object.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return True iff the given formula has been successfully proven.
     */
    public static boolean isProvable(Sequent toProve, Services services, int timeout) {
        return isProvable(toProve, services, false, timeout);
    }

    /**
     * Tries to prove the given formula with splitting and returns whether the prove could be
     * closed.
     *
     * @param toProve Sequent to prove.
     * @param services The services object.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return True iff the given formula has been successfully proven.
     */
    public static boolean isProvableWithSplitting(Sequent toProve, Services services, int timeout) {
        return isProvable(toProve, services, true, timeout);
    }

    /**
     * Tries to prove the equivalence of term1 and term2 and throws a {@link RuntimeException} if
     * the proof fails.
     *
     * @param term1 First term to check.
     * @param term2 Second term to check.
     * @param services The services object.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     *
     * @throws RuntimeException iff proving the equivalence of term1 and term2 fails.
     */
    public static void assertEquivalent(Term term1, Term term2, Services services, int timeout) {
        TermBuilder tb = services.getTermBuilder();

        Term assertionForm = tb.and(tb.imp(term1, term2), tb.imp(term2, term1));
        if (!isProvableWithSplitting(assertionForm, services, timeout)) {
            throw new RuntimeException("Could not prove expected equivalence.");
        }
    }

    // /////////////////////////////////////////////////
    // ////////////// GENERAL LOGIC /////////////////
    // ////////////// (Simplification) /////////////////
    // /////////////////////////////////////////////////

    /**
     * Tries to simplifies the given {@link Term} in a side proof with splits. If this attempt is
     * successful, i.e. the number of atoms in the simplified formula is lower (and, if requested,
     * also the number of disjunctions), the simplified formula is returned; otherwise, the original
     * formula is returned.
     * <p>
     *
     * <i>Please note that using this method can consume a great amount of time!</i>
     *
     * @param parentProof The parent {@link Proof}.
     * @param term The {@link Term} to simplify.
     * @param countDisjunctions If set to true, the method also takes the number of disjunctions (in
     *        addition to the number of atoms) into account when judging about the complexity of the
     *        "simplified" formula.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return The simplified {@link Term} or the original term, if simplification was not
     *         successful.
     *
     * @see #simplify(Proof, Term, int)
     * @see SymbolicExecutionUtil#simplify(Proof, Term)
     */
    public static Term trySimplify(final Proof parentProof, final Term term,
            boolean countDisjunctions, int timeout) {

        try {
            Term simplified = simplify(parentProof, term, timeout);

            if (countAtoms(simplified) < countAtoms(term) && (!countDisjunctions
                    || countDisjunctions(simplified, false) < countDisjunctions(term, false))) {

                return simplified;
            }
        } catch (ProofInputException e) {
            // ignore exception
        }

        return term;

    }

    // //////////////////////////////////////////////
    // ////////////// GENERAL LOGIC /////////////////
    // ////////////// (Calculus) ///////////////////
    // //////////////////////////////////////////////

    /**
     * Deletes all formulae of the succedent / antecedent.
     *
     * @param goal Goal to delete formulae from.
     * @param antec If true, antecedent formulae are deleted, else succedent formulae.
     */
    public static void clearSemisequent(Goal goal, boolean antec) {
        final Semisequent semiseq =
            antec ? goal.sequent().antecedent() : goal.sequent().succedent();
        for (final SequentFormula f : semiseq) {
            final PosInOccurrence gPio = new PosInOccurrence(f, PosInTerm.getTopLevel(), antec);
            goal.removeFormula(gPio);
        }
    }

    /**
     * An equals method that, before the comparison, replaces all program locations in the supplied
     * arguments by their branch-unique versions.
     *
     * @param se1 First element to check equality (mod renaming) for.
     * @param se2 Second element to check equality (mod renaming) for.
     * @param goal The goal of the current branch (for getting branch-unique names).
     * @param services The Services object.
     * @return true iff source elements can be matched, considering branch-unique location names.
     */
    public static boolean equalsModBranchUniqueRenaming(SourceElement se1, SourceElement se2,
            Node node, Services services) {

        // Quick short cut for the special case where no program variables
        // have to be renamed.
        if (se1.equalsModRenaming(se2, new NameAbstractionTable())) {
            return true;
        }

        LocVarReplBranchUniqueMap replMap =
            new LocVarReplBranchUniqueMap(node, DefaultImmutableSet.nil());

        ProgVarReplaceVisitor replVisitor1 =
            new ProgVarReplaceVisitor((ProgramElement) se1, replMap, services);
        ProgVarReplaceVisitor replVisitor2 =
            new ProgVarReplaceVisitor((ProgramElement) se2, replMap, services);

        replVisitor1.start();
        replVisitor2.start();

        return replVisitor1.result().equalsModRenaming(replVisitor2.result(),
            new NameAbstractionTable());
    }

    // /////////////////////////////////////////////////
    // //////////////// MERGE RELATED //////////////////
    // /////////////////////////////////////////////////

    /**
     * Creates a path condition that is equivalent to the disjunction of the two supplied formulae,
     * but possibly simpler. In the ideal case, the returned formula can be literally shorter than
     * each of the two formulae; in this case, it consists of the common elements of those.
     * <p>
     *
     * The underlying idea is based upon the observation that many path conditions that should be
     * merged are conjunctions of mostly the same elements and, in addition, formulae phi and !phi
     * that vanish after creating the disjunction of the path conditions. The corresponding valid
     * formula is <code>(phi & psi) | (phi & !psi) <-> phi</code>
     * <p>
     *
     * For formulae that cannot be simplified by this law, the method performs two additional
     * steps:<br>
     * (1) it applies, if possible, distributivity to simplify the result<br>
     * (2) it checks whether the disjunction is already equivalent to the common parts of the
     * formulae only. This often happens when merging all branches that occur in symbolic
     * execution.<br>
     *
     * @param cond1 First path condition to merge.
     * @param cond2 Second path condition to merge.
     * @param services The services object.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return A path condition that is equivalent to the disjunction of the two supplied formulae,
     *         but possibly simpler.
     */
    public static Term createSimplifiedDisjunctivePathCondition(final Term cond1, final Term cond2,
            Services services, int simplificationTimeout) {

        if (cond1.equals(cond2)) {
            return cond1;
        }

        final TermBuilder tb = services.getTermBuilder();

        final CommonAndSpecificSubformulasResult commonAndSpecific =
            commonAndSpecificSubformulas(cond1, cond2, services);

        final LinkedHashSet<Term> cond1ConjElems = commonAndSpecific.specific1;
        final LinkedHashSet<Term> cond2ConjElems = commonAndSpecific.specific2;
        final LinkedHashSet<Term> equalElements = commonAndSpecific.common;

        assert !cond1ConjElems.isEmpty() && !cond2ConjElems.isEmpty()
                : "Possibly, this merge is not sound: Cannot find distinguishing formulas!";

        final Term commonElemsTerm = joinConjuctiveElements(equalElements, services);

        final Term disjunctionOfSpecificParts =
            tb.or(joinConjuctiveElements(cond1ConjElems, services),
                joinConjuctiveElements(cond2ConjElems, services));

        // Last try: Check if the disjunction of the specific parts is valid,
        // like in "(x < 0), (x >= 0)".
        if (isProvableWithSplitting(disjunctionOfSpecificParts, services, simplificationTimeout)) {
            return commonElemsTerm;
        } else {
            return tb.and(commonElemsTerm, disjunctionOfSpecificParts);
        }
    }

    /**
     * Computes a formula that implies pathCondition1 and, if pathCondition1 and pathCondition2 are
     * contradicting, does not imply pathCondition2. The computed formula is at most as complex as
     * pathCondition1. This so generated distinguishing formula is returned in the first element of
     * the pair; the "rest" is contained in the second. It always holds that the conjunction of the
     * first element of the pair and the second element of the pair is equivalent to pathCondition1.
     *
     * @param pathCondition1 The first formula to compute a distinguishing formula for.
     * @param pathCondition2 The second formula to compute a distinguishing formula for.
     * @param services The services object.
     * @return (1) A formula that implies pathCondition1 and, if pathCondition1 and pathCondition2
     *         are contradicting, does not imply pathCondition2, and (2) the "rest" of
     *         pathCondition1 that is common with pathCondition2.
     */
    public static Optional<Pair<Term, Term>> getDistinguishingFormula(Term pathCondition1,
            Term pathCondition2, Services services) {

        return getDistinguishingFormula(getConjunctiveElementsFor(pathCondition1),
            getConjunctiveElementsFor(pathCondition2), services);

    }

    /**
     * @see #getDistinguishingFormula(Term, Term, Services)
     */
    public static Optional<Pair<Term, Term>> getDistinguishingFormula(
            ArrayList<Term> conjElemsPathCond1, ArrayList<Term> conjElemsPathCond2,
            Services services) {

        final TermBuilder tb = services.getTermBuilder();

        final CommonAndSpecificSubformulasResult commonAndSpecific =
            commonAndSpecificSubformulas(conjElemsPathCond1, conjElemsPathCond2, services);

        final LinkedHashSet<Term> cond1SpecificElems = commonAndSpecific.specific1;
        final LinkedHashSet<Term> cond2SpecificElems = commonAndSpecific.specific2;
        final LinkedHashSet<Term> equalElements = commonAndSpecific.common;

        if (cond1SpecificElems.isEmpty() || cond2SpecificElems.isEmpty()) {
            return Optional.empty();
        }

        Term theOneDistinguishingTerm = null;
        for (final Term t : cond1SpecificElems) {
            List<Term> distCandidates = cond2SpecificElems.stream()
                    .filter(t1 -> t1.equals(tb.not(t)) || t.equals(tb.not(t1)))
                    .collect(Collectors.toList());
            if (!distCandidates.isEmpty()) {
                // Just take the first, any one should be good enough, at least
                // with the present knowledge
                theOneDistinguishingTerm = t;
            }
        }

        return Optional.of(new Pair<>(
            theOneDistinguishingTerm != null ? theOneDistinguishingTerm
                    : joinConjuctiveElements(cond1SpecificElems, services),
            joinConjuctiveElements(equalElements, services)));

    }

    /**
     * Checks if two given path conditions are distinguishable.
     *
     * @param pathCondition1 First path condition to check.
     * @param pathCondition2 Second path condition to check.
     * @param services The services object.
     * @return True iff the two given path conditions are distinguishable.
     */
    public static boolean pathConditionsAreDistinguishable(Term pathCondition1, Term pathCondition2,
            Services services) {
        Optional<Pair<Term, Term>> distinguishingAndEqualFormula1 =
            getDistinguishingFormula(pathCondition1, pathCondition2, services);
        Optional<Pair<Term, Term>> distinguishingAndEqualFormula2 =
            getDistinguishingFormula(pathCondition2, pathCondition1, services);

        return distinguishingAndEqualFormula1.isPresent()
                || distinguishingAndEqualFormula2.isPresent();
    }

    /**
     * Closes the given partner goal, using the {@link CloseAfterMerge} rule.
     *
     * @param mergeNodeParent Parent of remaining join node.
     * @param mergePartner Partner goal to close.
     * @param newNames The set of new names (of Skolem constants) introduced in the merge.
     */
    public static void closeMergePartnerGoal(Node mergeNodeParent, Goal mergePartner,
            PosInOccurrence pio, SymbolicExecutionState mergeState,
            SymbolicExecutionState mergePartnerState, Term pc, Set<Name> newNames) {

        InitConfig initConfig = mergeNodeParent.proof().getInitConfig();

        CloseAfterMerge closeRule = CloseAfterMerge.INSTANCE;
        RuleApp app = closeRule.createApp(pio, mergePartner.node(), mergeNodeParent, mergeState,
            mergePartnerState, pc, newNames);

        // Register rule if not done yet.
        // This avoids error messages of the form
        // "no justification found for rule...".
        if (initConfig.getJustifInfo().getJustification(closeRule) == null) {
            initConfig.registerRuleIntroducedAtNode(app, mergePartner.node(), true);
        }

        mergePartner.apply(app);
    }

    /**
     * Converts a sequent (given by goal & pos in occurrence) to an SE state (U,C). Thereby, all
     * program variables occurring in the symbolic state are replaced by branch-unique
     * correspondents in order to enable merging of different branches declaring local variables.
     * <p>
     *
     * @param goal Current goal.
     * @param pio Position of update-program counter formula in goal.
     * @param services The services object.
     * @return An SE state (U,C).
     * @see #sequentToSETriple(Goal, PosInOccurrence, Services)
     */
    public static SymbolicExecutionState sequentToSEPair(Node node, PosInOccurrence pio,
            Services services) {

        SymbolicExecutionStateWithProgCnt triple = sequentToSETriple(node, pio, services);

        return new SymbolicExecutionState(triple.first, triple.second, node);
    }

    /**
     * Converts a sequent (given by goal & pos in occurrence) to an SE state (U,C,p). Thereby, all
     * program variables occurring in the program counter and in the symbolic state are replaced by
     * branch-unique correspondents in order to enable merging of different branches declaring local
     * variables.
     * <p>
     *
     * The problem which makes this renaming necessary is the fact that when executing a program
     * like <code>int x; x = ...</code>, the variable x is renamed to x_1, x_2 and so on in
     * different branches, which makes a "normal" merging impossible. Branch unique names are
     * tracked in the LocationVariables when they are renamed in InnerVariableNamer. Soundness is
     * not effected by the switch to branch-unique names. However, merged nodes are then of course
     * potentially different from their predecessors concerning the involved local variable symbols.
     *
     * @param goal Current goal.
     * @param pio Position of update-program counter formula in goal.
     * @param services The services object.
     * @return An SE state (U,C,p).
     */
    public static SymbolicExecutionStateWithProgCnt sequentToSETriple(Node node,
            PosInOccurrence pio, Services services) {

        ImmutableList<SequentFormula> pathConditionSet = ImmutableSLList.nil();
        pathConditionSet = pathConditionSet.prepend(node.sequent().antecedent().asList());

        Term selected = pio.subTerm();

        for (SequentFormula sf : node.sequent().succedent()) {
            if (!sf.formula().equals(selected)) {
                pathConditionSet = pathConditionSet
                        .prepend(new SequentFormula(services.getTermBuilder().not(sf.formula())));
            }
        }

        Term updateTerm = null;
        Term programCounter = null;

        if (selected.op() instanceof UpdateApplication) {
            updateTerm = selected.sub(0);
            programCounter = selected.sub(1);
        }

        return new SymbolicExecutionStateWithProgCnt(updateTerm, // Update
            joinListToAndTerm(pathConditionSet, services), // Path Condition
            programCounter, // Program Counter and Post Condition
            node); // CorrespondingNode
    }

    /**
     * Convenience method for converting a whole list of goal-pio combinations to symbolic execution
     * states; relies on {@link #sequentToSETriple(Node, PosInOccurrence, Services)}.
     *
     * @param sequentInfos Goals and PosInOccurrences specifying merge partners and the positions of
     *        the program counter-post condition formulae in the goals.
     * @return A list of symbolic execution states.
     */
    public static ImmutableList<SymbolicExecutionState> sequentsToSEPairs(
            Iterable<MergePartner> sequentInfos) {
        ImmutableList<SymbolicExecutionState> result = ImmutableSLList.nil();
        for (MergePartner sequentInfo : sequentInfos) {
            final Node node = sequentInfo.getGoal().node();
            final Services services = sequentInfo.getGoal().proof().getServices();

            Triple<Term, Term, Term> partnerSEState =
                sequentToSETriple(node, sequentInfo.getPio(), services);

            result = result.prepend(
                new SymbolicExecutionState(partnerSEState.first, partnerSEState.second, node));
        }

        return result;
    }

    /**
     * Due to the introduction of local namespaces, we run into trouble when applying state merging
     * in the presence of locally introduced symbols. These include program variables as well as
     * Skolem constants. This method finds all name clashes and renames the corresponding entities
     * in the {@link SymbolicExecutionState} state.
     *
     * @param mergeState The {@link SymbolicExecutionState} in which the partners should be merged.
     * @param mergePartnerState The {@link SymbolicExecutionState} of the second merge partner.
     * @param services The {@link Services} object.
     *
     * @return The renamed {@link SymbolicExecutionState} of the second merge partner.
     */
    public static Pair<SymbolicExecutionState, SymbolicExecutionState> handleNameClashes(
            SymbolicExecutionState mergeState, SymbolicExecutionState mergePartnerState,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Proof proof = services.getProof();

        // This goal
        final Collection<Operator> thisGoalSymbols = new ArrayList<>();
        final Goal thisGoal = proof.getOpenGoal(mergeState.getCorrespondingNode());
        final NamespaceSet thisGoalNamespaces = thisGoal.getLocalNamespaces();
        thisGoalSymbols.addAll(thisGoalNamespaces.programVariables().allElements());
        thisGoalSymbols.addAll(thisGoalNamespaces.functions().allElements());
        final List<Name> thisGoalNames =
            thisGoalSymbols.parallelStream().map(Named::name).collect(Collectors.toList());

        // Partner goal
        final Collection<Operator> partnerGoalSymbols = new ArrayList<>();
        final Goal partnerGoal = proof.getOpenGoal(mergePartnerState.getCorrespondingNode());
        final NamespaceSet partnerGoalNamespaces = partnerGoal.getLocalNamespaces();
        partnerGoalSymbols.addAll(partnerGoalNamespaces.programVariables().allElements());
        partnerGoalSymbols.addAll(partnerGoalNamespaces.functions().allElements());
        final List<Name> partnerGoalNames =
            partnerGoalSymbols.parallelStream().map(Named::name).collect(Collectors.toList());

        // Construct intersection: Common names
        thisGoalNames.retainAll(partnerGoalNames);

        if (!thisGoalNames.isEmpty()) {
            // There are conflicts... So let's do something

            final List<Operator> problematicOps =
                partnerGoalSymbols.parallelStream().filter(pv -> thisGoalNames.contains(pv.name()))
                        .filter(pv -> !thisGoalSymbols.contains(pv)).collect(Collectors.toList());

            // Loop over all problematic operators and rename them in the
            // partner state.
            for (Operator partnerStateOp : problematicOps) {
                final Operator mergeStateOp = thisGoalSymbols.parallelStream()
                        .filter(s -> s.name().equals(partnerStateOp.name()))
                        .collect(Collectors.toList()).get(0);

                Operator newOp1;
                Operator newOp2;
                if (partnerStateOp instanceof Function) {
                    newOp1 = ((Function) mergeStateOp)
                            .rename(new Name(tb.newName(partnerStateOp.name().toString(),
                                thisGoal.getLocalNamespaces())));
                    thisGoalNamespaces.functions().add((Function) newOp1);
                    thisGoalNamespaces.flushToParent();

                    newOp2 = ((Function) partnerStateOp)
                            .rename(new Name(tb.newName(partnerStateOp.name().toString(),
                                thisGoal.getLocalNamespaces())));
                    thisGoalNamespaces.functions().add((Function) newOp2);
                    thisGoalNamespaces.flushToParent();
                } else if (partnerStateOp instanceof LocationVariable) {
                    newOp1 = ((LocationVariable) mergeStateOp)
                            .rename(new Name(tb.newName(partnerStateOp.name().toString(),
                                thisGoal.getLocalNamespaces())));
                    thisGoalNamespaces.programVariables().add((LocationVariable) newOp1);
                    thisGoalNamespaces.flushToParent();

                    newOp2 = ((LocationVariable) partnerStateOp)
                            .rename(new Name(tb.newName(partnerStateOp.name().toString(),
                                thisGoal.getLocalNamespaces())));
                    thisGoalNamespaces.programVariables().add((LocationVariable) newOp2);
                    thisGoalNamespaces.flushToParent();
                } else {
                    throw new RuntimeException(
                        "MergeRule: Unexpected type of Operator involved in name clash: "
                            + partnerStateOp.getClass().getSimpleName());
                }

                mergeState = new SymbolicExecutionState(
                    OpReplacer.replace(mergeStateOp, newOp1, mergeState.getSymbolicState(), tb.tf(),
                        proof),
                    OpReplacer.replace(mergeStateOp, newOp1, mergeState.getPathCondition(), tb.tf(),
                        proof),
                    mergeState.getCorrespondingNode());

                mergePartnerState = new SymbolicExecutionState(
                    OpReplacer.replace(partnerStateOp, newOp2, mergePartnerState.getSymbolicState(),
                        tb.tf(), proof),
                    OpReplacer.replace(partnerStateOp, newOp2, mergePartnerState.getPathCondition(),
                        tb.tf(), proof),
                    mergePartnerState.getCorrespondingNode());
            }
        }

        return new Pair<>(mergeState, mergePartnerState);
    }

    /**
     * Parses a declaration of the type "&lt;SORT&gt; &lt;NAME&gt;", where &lt;SORT&gt; must be a
     * sort known to the proof and &lt;NAME&gt; must be a fresh name. This method is used, for
     * instance, in the GUI dialog for predicate abstraction. The parsed placeholder is registered
     * in KeY's namespaces.
     *
     * @param input Input to parse.
     * @param services The services object.
     * @return A pair of parsed sort and name for the placeholder.
     * @throws NameAlreadyBoundException If the given placeholder is already known to the system.
     * @throws SortNotKnownException If the given sort is not known to the system.
     */
    public static Pair<Sort, Name> parsePlaceholder(String input, Services services) {
        return parsePlaceholder(input, true, services);
    }

    /**
     * Parses a declaration of the type "&lt;SORT&gt; &lt;NAME&gt;", where &lt;SORT&gt; must be a
     * sort known to the proof and &lt;NAME&gt; must be a fresh name. This method is used, for
     * instance, in the GUI dialog for predicate abstraction. The parsed placeholder is registered
     * in KeY's namespaces iff registerInNamespaces is true.
     *
     * @param input Input to parse.
     * @param registerInNamespaces Flag to indicate whether the parsed placeholder should be
     *        registered in the namespaces.
     * @param services The services object.
     * @return A pair of parsed sort and name for the placeholder.
     * @throws NameAlreadyBoundException If the given placeholder is already known to the system.
     * @throws SortNotKnownException If the given sort is not known to the system.
     */
    public static Pair<Sort, Name> parsePlaceholder(String input, boolean registerInNamespaces,
            Services services) {
        String[] chunks = input.split(" ");
        if (chunks.length != 2) {
            throw new RuntimeException("Expecting an input of type &lt;SORT&gt; &lt;NAME&gt;");
        }

        Sort sort = services.getNamespaces().sorts().lookup(chunks[0]);

        if (sort == null) {
            throw new SortNotKnownException("Sort \"" + chunks[0] + "\" is not known");
        }

        String strName = chunks[1];
        Name name = new Name(strName);

        if (registerInNamespaces && services.getNamespaces().lookup(name) != null) {
            throw new NameAlreadyBoundException("The name \"" + strName
                + "\" is already known to the system.<br/>\n" + "Plase choose a fresh one.");
        }

        return new Pair<>(sort, name);
    }

    /**
     * Parses an abstraction predicate. The parameter input should be a textual representation of a
     * formula containing exactly one of the also supplied placeholders (but the contained
     * placeholder may have multiple occurrences in the formula). The result is an abstraction
     * predicate mapping terms of the type of the placeholder to the parsed predicate with the
     * placeholder substituted by the argument term.
     *
     * @param input The predicate to parse (contains exactly one placeholder).
     * @param localNamespaces The local {@link NamespaceSet}.
     * @return The parsed {@link AbstractionPredicate}.
     * @throws ParserException If there is a syntax error.
     */
    public static AbstractionPredicate parsePredicate(String input,
            ArrayList<Pair<Sort, Name>> registeredPlaceholders, NamespaceSet localNamespaces,
            Services services) throws ParserException {
        DefaultTermParser parser = new DefaultTermParser();
        Term formula = parser.parse(new StringReader(input), Sort.FORMULA, services,
            localNamespaces, services.getProof().abbreviations());

        ImmutableSet<LocationVariable> containedLocVars =
            MergeRuleUtils.getLocationVariables(formula, services);

        int nrContainedPlaceholders = 0;
        LocationVariable usedPlaceholder = null;
        for (Pair<Sort, Name> placeholder : registeredPlaceholders) {
            LocationVariable placeholderVariable = (LocationVariable) (services.getNamespaces()
                    .programVariables().lookup(placeholder.second));

            if (containedLocVars.contains(placeholderVariable)) {
                nrContainedPlaceholders++;
                usedPlaceholder = placeholderVariable;
            }
        }

        if (nrContainedPlaceholders != 1) {
            throw new RuntimeException(
                "An abstraction predicate must contain exactly one placeholder.");
        }

        return AbstractionPredicate.create(formula, usedPlaceholder, services);
    }

    // /////////////////////////////////////////////////
    // /////////////////// PRIVATE /////////////////////
    // /////////////////////////////////////////////////

    /**
     * Anonymizes all program variables occurring in the given term. If x is a PV in the term, the
     * result will be of the form <code>{ ... || x := vx || ...} term</code> where vx is a fresh
     * variable. Returns all free variables of the new termin the second component of the pair.
     *
     * @param term Term to anonymize.
     * @param services The services object.
     * @return A term of the form <code>{ ... || x := vx || ...} term</code> for every PV x
     *         occurring in the term, where vx is a fresh variable.
     */
    private static Pair<Term, ImmutableSet<QuantifiableVariable>> anonymizeProgramVariables(
            final Term term, final Services services) {
        TermBuilder tb = services.getTermBuilder();

        ImmutableSet<QuantifiableVariable> freeVars = term.freeVars();
        ImmutableList<Term> elementaries = ImmutableSLList.nil();

        for (LocationVariable loc : getLocationVariables(term, services)) {
            final String newName = tb.newName(stripIndex(loc.name().toString()));
            final LogicVariable newVar = new LogicVariable(new Name(newName), loc.sort());
            services.getNamespaces().variables().add(newVar);

            freeVars = freeVars.add(newVar);

            elementaries = elementaries.prepend(tb.elementary(tb.var(loc), tb.var(newVar)));
        }

        return new Pair<>(
            tb.apply(tb.parallel(elementaries), term), freeVars);
    }

    /**
     * Joins a list of sequent formulae to an and-connected term.
     *
     * @param formulae Formulae to join.
     * @param services The services object.
     * @return And-formula connecting the given terms.
     */
    private static Term joinListToAndTerm(ImmutableList<SequentFormula> formulae,
            Services services) {
        if (formulae.size() == 0) {
            return services.getTermBuilder().tt();
        } else if (formulae.size() == 1) {
            return formulae.head().formula();
        } else {
            return services.getTermBuilder().and(formulae.head().formula(),
                joinListToAndTerm(formulae.tail(), services));
        }
    }

    /**
     * Returns all used program locations in the given term. The term must be of the form \<{ ...
     * }\> phi (or \[{ ... }\] phi).
     *
     * @param programCounterTerm The term (program counter) to extract locations from.
     * @param services The Services object.
     * @return The set of contained program locations.
     */
    private static ImmutableSet<LocationVariable> getProgramLocations(Term programCounterTerm,
            Services services) {
        CollectLocationVariablesVisitor visitor =
            new CollectLocationVariablesVisitor(programCounterTerm.javaBlock().program(), services);

        ImmutableSet<LocationVariable> progVars = DefaultImmutableSet.nil();

        // Collect program variables in Java block
        visitor.start();
        progVars = progVars.union(visitor.getLocationVariables());

        return progVars;
    }

    /**
     * Returns all used program locations in the given term. The term must be of the form \<{ ...
     * }\> phi (or \[{ ... }\] phi).
     *
     * @param programCounterTerm The term (program counter) to extract locations from.
     * @param services The Services object.
     * @return The set of contained program locations.
     */
    private static HashSet<LocationVariable> getProgramLocationsHashSet(Term programCounterTerm,
            Services services) {
        final JavaProgramElement program = programCounterTerm.javaBlock().program();
        if (program instanceof StatementBlock && (((StatementBlock) program).isEmpty()
                || (((StatementBlock) program).getInnerMostMethodFrame() != null
                        && ((StatementBlock) program).getInnerMostMethodFrame().getBody()
                                .isEmpty()))) {
            return new HashSet<>();
        }

        CollectLocationVariablesVisitorHashSet visitor =
            new CollectLocationVariablesVisitorHashSet(program, services);

        // Collect program variables in Java block
        visitor.start();
        return visitor.getLocationVariables();
    }

    /**
     * Joins a list of formulae to a conjunction.
     *
     * @param elems Formulae to join.
     * @param services The services object.
     * @return A conjunction of the supplied formulae.
     */
    private static Term joinConjuctiveElements(final Collection<Term> elems, Services services) {
        TermBuilder tb = services.getTermBuilder();

        if (elems.isEmpty()) {
            return tb.tt();
        }

        Iterator<Term> it = elems.iterator();

        Term result = it.next();
        while (it.hasNext()) {
            result = tb.and(result, it.next());
        }

        return result;
    }

    /**
     * Tries to prove the given formula and returns the result.
     *
     * @param toProve Formula to prove.
     * @param services The services object.
     * @param doSplit if true, splitting is allowed (normal mode).
     * @param sideProofName name for the generated side proof.
     * @param timeout A timeout for the proof in milliseconds.
     * @return The proof result.
     */
    private static ApplyStrategyInfo tryToProve(Term toProve, Services services, boolean doSplit,
            String sideProofName, int timeout) throws ProofInputException {
        return tryToProve(Sequent.createSequent(
            // Sequent to prove
            Semisequent.EMPTY_SEMISEQUENT, new Semisequent(new SequentFormula(toProve))), services,
            doSplit, sideProofName, timeout);
    }

    /**
     * Tries to prove the given formula and returns the result.
     *
     * @param toProve Sequent to prove.
     * @param services The services object.
     * @param doSplit if true, splitting is allowed (normal mode).
     * @param sideProofName name for the generated side proof.
     * @param timeout A timeout for the proof in milliseconds. Set to -1 for no timeout.
     * @return The proof result.
     */
    private static ApplyStrategyInfo tryToProve(Sequent toProve, Services services, boolean doSplit,
            String sideProofName, int timeout) throws ProofInputException {
        final ProofEnvironment sideProofEnv =
            SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());

        ProofStarter proofStarter = SideProofUtil.createSideProof(sideProofEnv, // Proof
            // environment
            toProve, sideProofName); // Proof name

        proofStarter.setTimeout(timeout);
        proofStarter.setStrategyProperties(setupStrategy());

        return proofStarter.start();
    }

    /**
     * creates the strategy configuration to be used for the side proof
     *
     * @return the StrategyProperties
     */
    private static StrategyProperties setupStrategy() {
        final StrategyProperties sp = new StrategyProperties();
        sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY,
            StrategyProperties.AUTO_INDUCTION_OFF);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
            StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
            StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
            StrategyProperties.SPLITTING_NORMAL);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
        sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY,
            StrategyProperties.CLASS_AXIOM_OFF);
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE);
        sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
        return sp;
    }

    /**
     * Tries to prove the given formula and returns whether the proof could be closed.
     *
     * @param toProve Formula to prove.
     * @param services The services object.
     * @param doSplit if true, splitting is allowed (normal mode).
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return True iff the given formula has been successfully proven.
     */
    private static boolean isProvable(Term toProve, Services services, boolean doSplit,
            int timeout) {
        try {
            final ApplyStrategyInfo proofResult =
                tryToProve(toProve, services, doSplit, "Provability check", timeout);
            return proofResult.getProof().closed();
        } catch (ProofInputException pie) {
            // internal error
            LOGGER.warn("Internal error", pie);
        }
        return false;
    }

    /**
     * Tries to prove the given formula and returns whether the prove could be closed.
     *
     * @param toProve Sequent to prove.
     * @param services The services object.
     * @param doSplit if true, splitting is allowed (normal mode).
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return True iff the given formula has been successfully proven.
     */
    private static boolean isProvable(Sequent toProve, Services services, boolean doSplit,
            int timeout) {
        try {
            final ApplyStrategyInfo proofResult =
                tryToProve(toProve, services, doSplit, "Provability check", timeout);
            return proofResult.getProof().closed();
        } catch (ProofInputException pie) {
            // internal error
            LOGGER.warn("Internal error", pie);
        }
        return false;
    }

    /**
     * Simplifies the given {@link Term} in a side proof with splits. This code has been copied from
     * {@link SymbolicExecutionUtil} and only been slightly modified (to allow for splitting the
     * proof).
     *
     * @param parentProof The parent {@link Proof}.
     * @param term The {@link Term} to simplify.
     * @param timeout Time in milliseconds after which the side proof is aborted.
     * @return The simplified {@link Term}.
     * @throws ProofInputException Occurred Exception.
     *
     * @see SymbolicExecutionUtil#simplify(Proof, Term)
     */
    private static Term simplify(Proof parentProof, Term term, int timeout)
            throws ProofInputException {

        final Services services = parentProof.getServices();

        final ApplyStrategyInfo info =
            tryToProve(term, services, true, "Term simplification", timeout);

        // The simplified formula is the conjunction of all open goals
        ImmutableList<Goal> openGoals = info.getProof().openEnabledGoals();
        final TermBuilder tb = services.getTermBuilder();
        if (openGoals.isEmpty()) {
            return tb.tt();
        } else {
            ImmutableList<Term> goalImplications = ImmutableSLList.nil();
            for (Goal goal : openGoals) {
                Term goalImplication = sequentToFormula(goal.sequent(), services);
                goalImplications = goalImplications.append(goalImplication);
            }

            return tb.and(goalImplications);
        }
    }

    /**
     * Converts a Sequent "Gamma ==> Delta" into a single formula equivalent to "/\ Gamma -> \/
     * Delta"; however, the formulae in Gamma are shifted to the succedent by the negation-left
     * rule, so the result of this method is a disjunction, not an implication.
     *
     * @param sequent The sequent to convert to a formula.
     * @param services The services object.
     * @return A formula equivalent to the given sequent.
     */
    private static Term sequentToFormula(Sequent sequent, Services services) {
        TermBuilder tb = services.getTermBuilder();

        ImmutableList<Term> negAntecedentForms = ImmutableSLList.nil();
        ImmutableList<Term> succedentForms = ImmutableSLList.nil();

        // Shift antecedent formulae to the succedent by negation
        for (SequentFormula sf : sequent.antecedent().asList()) {
            negAntecedentForms = negAntecedentForms.prepend(tb.not(sf.formula()));
        }

        for (SequentFormula sf : sequent.succedent().asList()) {
            succedentForms = succedentForms.prepend(sf.formula());
        }

        return tb.or(negAntecedentForms.prepend(succedentForms));
    }

    /**
     * Tells whether a name is unique in the passed list of global variables.
     *
     * @param name The name to check uniqueness for.
     * @param globals The global variables for the givan branch.
     * @see VariableNamer#isUniqueInGlobals(String, Iterable)
     */
    private static boolean isUniqueInGlobals(String name, Iterable<IProgramVariable> globals) {
        for (final IProgramVariable n : globals) {
            if (n.toString().equals(name)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Looks up a program variable by its name in the PV namespace.
     *
     * @param name Name to find a PV for.
     * @return The PV with the given name in the global namespace, or null if there is none.
     */
    private static LocationVariable lookupVarInNS(String name, Services services) {
        return (LocationVariable) services.getNamespaces().programVariables()
                .lookup(new Name(name));
    }

    /**
     * Returns the set of specific and common conjunctive subformulas of two formulas. For instance,
     * if cond1 = "phi & psi" and cond2 = "phi & psi'", the specific parts will be "psi" and "psi'",
     * respectively, while the common part will be "phi".
     *
     * @param cond1 The conjunctive elements of the first formula.
     * @param cond2 The conjunctive elements of the second formula.
     * @param services The {@link Services} object.
     * @return The common and specific parts for cond1 and cond2.
     * @see #commonAndSpecificSubformulas(ArrayList, ArrayList, Services)
     */
    private static CommonAndSpecificSubformulasResult commonAndSpecificSubformulas(final Term cond1,
            final Term cond2, Services services) {
        return commonAndSpecificSubformulas(getConjunctiveElementsFor(cond1),
            getConjunctiveElementsFor(cond2), services);
    }

    /**
     * Returns the set of specific and common conjunctive subformulas of two formulas. For instance,
     * if cond1 = "phi & psi" and cond2 = "phi & psi'", the specific parts will be "psi" and "psi'",
     * respectively, while the common part will be "phi".
     *
     * @param cond1 The first formula.
     * @param cond2 The second formula.
     * @param services The {@link Services} object.
     * @return The common and specific parts for cond1 and cond2.
     */
    private static CommonAndSpecificSubformulasResult commonAndSpecificSubformulas(
            final ArrayList<Term> cond1, final ArrayList<Term> cond2, Services services) {
        final LinkedHashSet<Term> cond1ConjElems = new LinkedHashSet<>(cond1);
        final LinkedHashSet<Term> cond2ConjElems = new LinkedHashSet<>(cond2);

        // Calculate the equal elements (i.e., the intersection)
        final LinkedHashSet<Term> equalElements = new LinkedHashSet<>(cond1ConjElems);
        equalElements.retainAll(cond2ConjElems);

        // Subtract those from the conjunctive elements of both path conditions,
        // such that those only contain the specific parts
        cond1ConjElems.removeAll(equalElements);
        cond2ConjElems.removeAll(equalElements);

        return new CommonAndSpecificSubformulasResult(cond1ConjElems, cond2ConjElems,
            equalElements);
    }

    // /////////////////////////////////////////////////
    // /////////////////// CLASSES /////////////////////
    // /////////////////////////////////////////////////

    /**
     * Creates {@link TermWrapper} objects, thereby ensuring that equal term wrappers also have
     * equal hash codes.
     *
     * @author Dominic Scheurer
     */
    static class TermWrapperFactory {
        private final ArrayList<Term> wrappedTerms = new ArrayList<>();

        public TermWrapper wrapTerm(Term term) {
            for (Term existingTerm : wrappedTerms) {
                if (existingTerm.equalsModRenaming(term)) {
                    return new TermWrapper(term, existingTerm.hashCode());
                }
            }

            wrappedTerms.add(term);
            return new TermWrapper(term, term.hashCode());
        }
    }

    /**
     *
     * TODO
     *
     * @author Dominic Scheurer
     */
    private static class CommonAndSpecificSubformulasResult {
        public final LinkedHashSet<Term> specific1, specific2, common;

        public CommonAndSpecificSubformulasResult(LinkedHashSet<Term> specific1,
                LinkedHashSet<Term> specific2, LinkedHashSet<Term> common) {
            this.specific1 = specific1;
            this.specific2 = specific2;
            this.common = common;
        }
    }

    /**
     * Simple term wrapper for comparing terms modulo renaming.
     *
     * @author Dominic Scheurer
     * @see TermWrapperFactory
     */
    static class TermWrapper {
        private final Term term;
        private final int hashcode;

        public TermWrapper(Term term, int hashcode) {
            this.term = term;
            this.hashcode = hashcode;
        }

        public Term getTerm() {
            return term;
        }

        @Override
        public boolean equals(Object obj) {
            return obj instanceof TermWrapper
                    && term.equalsModRenaming(((TermWrapper) obj).getTerm());
        }

        @Override
        public int hashCode() {
            return hashcode;
        }

        @Override
        public String toString() {
            return term.toString();
        }

        /**
         * Adds the wrapped content of the Iterable object into the given target collection.
         *
         * @param target The collection to insert the wrapped terms into.
         * @param wrappedCollection Iterable to transform.
         * @return The target collection with inserted terms.
         */
        public static <T extends Collection<Term>> T toTermList(T target,
                Iterable<TermWrapper> wrappedCollection) {

            for (TermWrapper termWrapper : wrappedCollection) {
                target.add(termWrapper.getTerm());
            }

            return target;
        }
    }

    /**
     * Visitor for collecting program locations in a Java block.
     *
     * @author Dominic Scheurer
     */
    private static class CollectLocationVariablesVisitor extends JavaASTVisitor {
        private ImmutableSet<LocationVariable> variables = DefaultImmutableSet.nil();

        public CollectLocationVariablesVisitor(ProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(final SourceElement node) {
            // ignore
        }

        @Override
        public void performActionOnLocationVariable(LocationVariable x) {
            variables = variables.add(x);
        }

        /**
         * Call start() before calling this method!
         *
         * @return All program locations in the given Java block.
         */
        public ImmutableSet<LocationVariable> getLocationVariables() {
            return variables;
        }
    }

    /**
     * Visitor for collecting program locations in a Java block.
     *
     * @author Dominic Scheurer
     */
    private static class CollectLocationVariablesVisitorHashSet extends JavaASTVisitor {
        private final HashSet<LocationVariable> variables = new HashSet<>();

        public CollectLocationVariablesVisitorHashSet(ProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(final SourceElement node) {
            // ignore
        }

        @Override
        public void performActionOnLocationVariable(LocationVariable x) {
            variables.add(x);
        }

        /**
         * Call start() before calling this method!
         *
         * @return All program locations in the given Java block.
         */
        public HashSet<LocationVariable> getLocationVariables() {
            return variables;
        }
    }

    /**
     * Map for renaming variables to their branch-unique names. Putting things into this map has
     * absolutely no effect; the get method just relies on the
     * {@link LocationVariable#getBranchUniqueName()} method of the respective location variable.
     * Therefore, this map is also a singleton object.
     *
     * @author Dominic Scheurer
     */
    private static class LocVarReplBranchUniqueMap
            extends HashMap<ProgramVariable, ProgramVariable> {
        private static final long serialVersionUID = 2305410114265133879L;

        private final Node node;
        private final ImmutableSet<LocationVariable> doNotRename;
        private final HashMap<LocationVariable, ProgramVariable> cache =
            new HashMap<>();

        public LocVarReplBranchUniqueMap(Node goal, ImmutableSet<LocationVariable> doNotRename) {
            this.node = goal;
            this.doNotRename = doNotRename;
        }

        @Override
        public boolean isEmpty() {
            return false;
        }

        @Override
        public boolean containsKey(Object key) {
            return key instanceof LocationVariable;
        }

        @Override
        public boolean containsValue(Object value) {
            return false;
        }

        @Override
        public ProgramVariable get(Object key) {
            if (key instanceof LocationVariable) {
                LocationVariable var = (LocationVariable) key;

                if (doNotRename.contains(var)) {
                    return var;
                }

                if (cache.containsKey(var)) {
                    return cache.get(var);
                }

                final ProgramVariable result = getBranchUniqueLocVar(var, node);
                cache.put(var, result);

                return result;
            } else {
                return null;
            }
        }

        @Override
        public ProgramVariable put(ProgramVariable key, ProgramVariable value) {
            return null;
        }

        @Override
        public ProgramVariable remove(Object key) {
            return null;
        }

        @Override
        public Set<ProgramVariable> keySet() {
            return null;
        }

        @Override
        public Collection<ProgramVariable> values() {
            return null;
        }

        @Override
        public Set<java.util.Map.Entry<ProgramVariable, ProgramVariable>> entrySet() {
            return null;
        }
    }

    /**
     * This exception is thrown by methods to indicate that a given KeY sort is not known in the
     * current situation.
     */
    static class SortNotKnownException extends RuntimeException {
        private static final long serialVersionUID = -5728194402773352846L;

        public SortNotKnownException(String message) {
            super(message);
        }
    }

    /**
     * This exception is thrown by methods to indicate that a name for which it is requested to
     * register it is already known to the system.
     */
    static class NameAlreadyBoundException extends RuntimeException {
        private static final long serialVersionUID = -2406984399754204833L;

        public NameAlreadyBoundException(String message) {
            super(message);
        }
    }
}
