// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.joinrule;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.join.CloseAfterJoin;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

/**
 * This class encapsulates static methods used in the JoinRule implementation.
 * The methods are organized into different sections (see comments):
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
 * <li>JOIN RELATED</li>
 * <li>PRIVATE</li>
 * </ol>
 * 
 * Feel free to make private methods publicly visible if you need them.
 * 
 * @author Dominic Scheurer
 */
public class JoinRuleUtils {

    //////////////////////////////////////////////////
    /////////////// SIMPLE AUXILIARIES ///////////////
    //////////////////////////////////////////////////

    /**
     * For Strings "xxx_i", this method returns "xxx". For Strings without the
     * underscore, the original String is returned.
     * 
     * @param name
     *            Name to remove the index from.
     * @return The name without the index, if any.
     */
    public static String stripIndex(String name) {
        int underscoreOccurrence = name.indexOf('_');
        if (underscoreOccurrence > -1) {
            return name.substring(0, underscoreOccurrence);
        }
        else {
            return name;
        }
    }

    ///////////////////////////////////////////////////
    ////////////////// GENERAL LOGIC //////////////////
    //////////////////   (Syntax)    //////////////////
    ///////////////////////////////////////////////////

    /**
     * @param u
     *            The update (in normal form) to extract program locations from.
     * @return All program locations (left sides) in the given update.
     */
    public static ImmutableSet<LocationVariable> getUpdateLeftSideLocations(
            Term u) {
        if (u.op() instanceof ElementaryUpdate) {

            ImmutableSet<LocationVariable> result = DefaultImmutableSet.nil();
            result = result.add((LocationVariable) ((ElementaryUpdate) u.op())
                    .lhs());
            return result;

        }
        else if (u.op() instanceof UpdateJunctor) {

            ImmutableSet<LocationVariable> result = DefaultImmutableSet.nil();
            for (Term sub : u.subs()) {
                result = result.union(getUpdateLeftSideLocations(sub));
            }
            return result;

        }
        else {

            throw new IllegalStateException("Update should be in normal form!");

        }
    }

    /**
     * Returns all program variables in the given term.
     * 
     * @param term
     *            The term to extract program variables from.
     * @return All program variables of the given term.
     */
    public static ImmutableSet<LocationVariable> getLocationVariables(
            Term term, Services services) {
        ImmutableSet<LocationVariable> result = DefaultImmutableSet.nil();

        if (term.op() instanceof LocationVariable) {
            result = result.add((LocationVariable) term.op());
        }
        else {
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
     * Returns all Skolem constants in the given term.
     * 
     * @param term
     *            The term to extract Skolem constants from.
     * @return All SkolemConstants of the given term.
     */
    public static HashSet<Function> getSkolemConstants(Term term) {
        HashSet<Function> result = new HashSet<Function>();

        if (term.op() instanceof Function
                && ((Function) term.op()).isSkolemConstant()) {
            result.add((Function) term.op());
        }
        else {
            for (Term sub : term.subs()) {
                result.addAll(getSkolemConstants(sub));
            }
        }

        return result;
    }

    /**
     * Returns the right side for a given location variable in an update (in
     * normal form).
     * 
     * @param update
     *            Update term to search.
     * @param leftSide
     *            Left side to find the right side for.
     * @return The right side in the update for the given left side.
     */
    public static Term getUpdateRightSideFor(Term update,
            LocationVariable leftSide) {
        if (update.op() instanceof ElementaryUpdate
                && ((ElementaryUpdate) update.op()).lhs().equals(leftSide)) {

            return update.sub(0);

        }
        else if (update.op() instanceof UpdateJunctor
                && update.op().equals(UpdateJunctor.PARALLEL_UPDATE)) {

            for (Term sub : update.subs()) {
                Term rightSide = getUpdateRightSideFor(sub, leftSide);
                if (rightSide != null) {
                    return rightSide;
                }
            }

            return null;

        }
        else {
            return null;
        }
    }

    /**
     * Counts the atoms in a formula.
     * 
     * @param term
     *            Formula to count atoms for.
     * @return Number of atoms in the formula
     * @throws IllegalArgumentException
     *             if the supplied term is not a formula
     */
    public static int countAtoms(Term term) {
        if (term.sort().equals(Sort.FORMULA)) {
            if (term.op() instanceof Junctor) {
                int result = 0;
                for (Term sub : term.subs()) {
                    result += countAtoms(sub);
                }
                return result;
            }
            else {
                return 1;
            }
        }
        else {
            throw new IllegalArgumentException(
                    "Can only compute atoms for formulae");
        }
    }

    /**
     * Counts the disjunctions in a formula.
     * 
     * @param term
     *            Formula to count disjunctions for.
     * @param negated
     *            Set to true iff the current subformula is in the scope of a
     *            negation; in this case, "and" junctors have the role of "or"
     *            junctors considering the disjunctive complexity.
     * @return Number of disjunctions in the formula
     * @throws IllegalArgumentException
     *             if the supplied term is not a formula
     */
    public static int countDisjunctions(Term term, boolean negated) {
        if (term.sort().equals(Sort.FORMULA)) {
            if (term.op() instanceof Junctor) {
                int result = 0;

                if (!negated && term.op().equals(Junctor.OR) || !negated
                        && term.op().equals(Junctor.IMP) || negated
                        && term.op().equals(Junctor.AND)) {
                    result++;
                }

                if (term.op().equals(Junctor.NOT)) {
                    negated = !negated;
                }

                for (Term sub : term.subs()) {
                    result += countDisjunctions(sub, negated);
                }

                return result;
            }
            else {
                return 0;
            }
        }
        else {
            throw new IllegalArgumentException(
                    "Can only compute atoms for formulae");
        }
    }

    /**
     * Computes and registers a new Skolem constant with the given prefix in its
     * name of the given sort.
     * 
     * @param prefix
     *            Prefix for the name of the constant.
     * @param sort
     *            Sort of the constant.
     * @param services
     *            The services object.
     * @return A new Skolem constant of the given sort with the given prefix in
     *         its name.
     */
    public static Function getNewSkolemConstantForPrefix(String prefix,
            Sort sort, Services services) {
        Function result = null;
        String newName = "";

        do {
            newName = services.getTermBuilder().newName(prefix);
            result = new Function(new Name(newName), sort, true);
            services.getNamespaces().functions().add(result);
        }
        while (newName.equals(prefix));

        return result;
    }

    /**
     * Computes and registers a fresh variable with the given prefix in its name
     * of the given sort.
     * 
     * @param prefix
     *            Prefix for the name of the variable.
     * @param sort
     *            Sort of the variable.
     * @param services
     *            The services object.
     * @return A fresh variable of the given sort with the given prefix in its
     *         name.
     */
    public static LogicVariable getFreshVariableForPrefix(String prefix,
            Sort sort, Services services) {
        LogicVariable result = null;
        String newName = "";

        do {
            newName = services.getTermBuilder().newName(prefix);
            result = new LogicVariable(new Name(newName), sort);
            services.getNamespaces().variables().add(result);
        }
        while (newName.equals(prefix));

        return result;
    }

    /**
     * Substitutes all constants in the given term by fresh variables. Multiple
     * occurrences of a constant are substituted by the same variable.
     * 
     * @param term
     *            Term in which to substitute constants by variables.
     * @param replMap
     *            Map from constants to variables in order to remember
     *            substitutions of one constant.
     * @return A term equal to the input, but with constants substituted by
     *         fresh variables.
     */
    public static Term substConstantsByFreshVars(Term term,
            HashMap<Function, LogicVariable> replMap, Services services) {
        return substConstantsByFreshVars(term, null, replMap, services);
    }

    /**
     * Substitutes all constants in the given term that are contained in the set
     * restrictTo by fresh variables. If restrictTo is null, then all constants
     * in the term are replaced. Multiple occurrences of a constant are
     * substituted by the same variable.
     * 
     * @param term
     *            Term in which to substitute constants by variables.
     * @param restrictTo
     *            Set of constants to replace. If null, all constants are
     *            replaced.
     * @param replMap
     *            Map from constants to variables in order to remember
     *            substitutions of one constant.
     * @return A term equal to the input, but with constants substituted by
     *         fresh variables.
     */
    public static Term substConstantsByFreshVars(Term term,
            HashSet<Function> restrictTo,
            HashMap<Function, LogicVariable> replMap, Services services) {
        TermBuilder tb = services.getTermBuilder();

        if (term.op() instanceof Function
                && ((Function) term.op()).isSkolemConstant()
                && (restrictTo == null || restrictTo.contains((Function) term
                        .op()))) {

            Function constant = (Function) term.op();

            if (!replMap.containsKey(constant)) {
                LogicVariable freshVariable = getFreshVariableForPrefix(
                        stripIndex(constant.toString()), constant.sort(),
                        services);
                replMap.put(constant, freshVariable);
            }

            return tb.var(replMap.get(constant));

        }
        else {

            LinkedList<Term> transfSubs = new LinkedList<Term>();
            for (Term sub : term.subs()) {
                transfSubs
                        .add(substConstantsByFreshVars(sub, replMap, services));
            }

            return services.getTermFactory().createTerm(term.op(),
                    new ImmutableArray<Term>(transfSubs), term.boundVars(),
                    term.javaBlock(), term.getLabels());

        }
    }

    /**
     * Existentially closes all logical and location variables in the given
     * term.
     * 
     * @param term
     *            Term to existentially close.
     * @param services
     *            The services object.
     * @return A new term which is equivalent to the existential closure of the
     *         argument term.
     */
    public static Term exClosure(final Term term, final Services services) {
        TermBuilder tb = services.getTermBuilder();
        Pair<Term, ImmutableSet<QuantifiableVariable>> anonymized = anonymizeProgramVariables(
                term, services);

        return tb.ex(anonymized.second, anonymized.first);
    }

    /**
     * Universally closes all logical and location variables in the given term.
     * 
     * @param term
     *            Term to universally close.
     * @param services
     *            The services object.
     * @return A new term which is equivalent to the universal closure of the
     *         argument term.
     */
    public static Term allClosure(final Term term, final Services services) {
        TermBuilder tb = services.getTermBuilder();
        Pair<Term, ImmutableSet<QuantifiableVariable>> anonymized = anonymizeProgramVariables(
                term, services);

        return tb.all(anonymized.second, anonymized.first);
    }

    /**
     * Checks if an update is of the form { x := v || ... || z := q}.
     * 
     * @param u
     *            Update to check.
     * @return true iff u is in normal form.
     */
    public static boolean isUpdateNormalForm(Term u) {
        if (u.op() instanceof ElementaryUpdate) {
            return true;
        }
        else if (u.op() instanceof UpdateJunctor) {
            boolean result = true;
            for (Term sub : u.subs()) {
                result = result && isUpdateNormalForm(sub);
            }
            return result;
        }
        else {
            return false;
        }
    }

    /**
     * Dissects a conjunction into its conjunctive elements.
     * 
     * @param term
     *            Conjunctive formula to dissect (may be a conjunction of one
     *            element, i.e. no "real" conjunction). In this case, the
     *            resulting list will contain exactly the supplied formula.
     * @return The conjunctive elements of the supplied formula.
     */
    public static ArrayList<Term> getConjunctiveElementsFor(final Term term) {
        ArrayList<Term> result = new ArrayList<Term>();

        if (term.op().equals(Junctor.AND)) {
            result.addAll(getConjunctiveElementsFor(term.sub(0)));
            result.addAll(getConjunctiveElementsFor(term.sub(1)));
        }
        else {
            result.add(term);
        }

        return result;
    }

    /**
     * Find a location variable for the given one that is unique for the branch
     * corresponding to the given goal, but not necessarily globally unique. The
     * variable with the first branch-unique name w.r.t. a numeric index is
     * returned.
     * 
     * @param var
     *            Variable to get a branch-unique correspondent for.
     * @param startLeaf
     *            The leaf of the branch.
     * @return The first indexed PV that is unique w.r.t. the given branch, but
     *         not with the global variable registry.
     */
    public static LocationVariable getBranchUniqueLocVar(LocationVariable var,
            Node startLeaf) {

        Services services = startLeaf.proof().getServices();

        // Find the node where the variable was introduced
        Node intrNode = getIntroducingNodeforLocVar(var, startLeaf);

        String base = stripIndex(var.name().toString());

        int newCounter = 0;
        String branchUniqueName = base;
        while (!isUniqueInGlobals(branchUniqueName.toString(),
                intrNode.getGlobalProgVars())
                || (lookupVarInNS(branchUniqueName, services) != null && !lookupVarInNS(
                        branchUniqueName, services).sort().equals(var.sort()))) {
            newCounter += 1;
            branchUniqueName = base + "_" + newCounter;
        }

        LocationVariable branchUniqueVar = lookupVarInNS(branchUniqueName,
                services);

        return branchUniqueVar == null ? var : branchUniqueVar;
    }

    /**
     * Finds the node, from the given leaf on, where the variable was
     * introduced.
     * 
     * @param var
     *            Variable to find introducing node for.
     * @param node
     *            Leaf to start from.
     * @return The node where the variable was introduced.
     */
    public static Node getIntroducingNodeforLocVar(LocationVariable var,
            Node node) {

        while (!node.root() && node.getGlobalProgVars().contains(var)) {
            node = node.parent();
        }

        return node;

    }

    /**
     * Returns the first Java block in the given term that can be found by
     * recursive search, or the empty block if there is no non-empty Java block
     * in the term.
     * 
     * @param term
     *            The term to extract Java blocks for.
     * @return The first Java block in the given term or the empty block if
     *         there is no non-empty Java block.
     */
    public static JavaBlock getJavaBlockRecursive(Term term) {
        if (!term.isContainsJavaBlockRecursive()) {
            return JavaBlock.EMPTY_JAVABLOCK;
        }

        if (term.subs().size() == 0 || !term.javaBlock().isEmpty()) {
            return term.javaBlock();
        }
        else {
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
     * Tries to prove the given formula without splitting and returns whether
     * the prove could be closed.
     * 
     * @param toProve
     *            Formula to prove.
     * @param services
     *            The services object.
     * @return True iff the given formula has been successfully proven.
     */
    public static boolean isProvable(Term toProve, Services services) {
        return isProvable(toProve, services, false);
    }

    /**
     * Tries to prove the given formula with splitting and returns whether the
     * prove could be closed.
     * 
     * @param toProve
     *            Formula to prove.
     * @param services
     *            The services object.
     * @return True iff the given formula has been successfully proven.
     */
    public static boolean isProvableWithSplitting(Term toProve,
            Services services) {
        return isProvable(toProve, services, true);
    }

    /**
     * Tries to prove the equivalence of term1 and term2 and throws a
     * {@link RuntimeException} if the proof fails.
     * 
     * @param term1
     *            First term to check.
     * @param term2
     *            Second term to check.
     * @param services
     *            The services object.
     * 
     * @throws RuntimeException
     *             iff proving the equivalence of term1 and term2 fails.
     */
    public static void assertEquivalent(Term term1, Term term2,
            Services services) {
        TermBuilder tb = services.getTermBuilder();

        Term assertionForm = tb.and(tb.imp(term1, term2), tb.imp(term2, term1));
        if (!isProvableWithSplitting(assertionForm, services)) {
            throw new RuntimeException("Could not prove expected equivalence.");
        }
    }

    // /////////////////////////////////////////////////
    // //////////////   GENERAL LOGIC  /////////////////
    // ////////////// (Simplification) /////////////////
    // /////////////////////////////////////////////////

    /**
     * Tries to simplifies the given {@link Term} in a side proof with splits.
     * If this attempt is successful, i.e. the number of atoms in the simplified
     * formula is lower (and, if requested, also the number of disjunctions),
     * the simplified formula is returned; otherwise, the original formula is
     * returned.
     * 
     * @param parentProof
     *            The parent {@link Proof}.
     * @param term
     *            The {@link Term} to simplify.
     * @param countDisjunctions
     *            If set to true, the method also takes the number of
     *            disjunctions (in addition to the number of atoms) into account
     *            when judging about the complexity of the "simplified" formula.
     * @return The simplified {@link Term} or the original term, if
     *         simplification was not successful.
     * 
     * @see #simplify(Proof, Term)
     * @see SymbolicExecutionUtil#simplify(Proof, Term)
     */
    public static Term trySimplify(final Proof parentProof, final Term term,
            boolean countDisjunctions) {

        try {
            Term simplified = simplify(parentProof, term);

            if (countAtoms(simplified) < countAtoms(term)
                    && (!countDisjunctions || countDisjunctions(simplified,
                            false) < countDisjunctions(term, false))) {

                return simplified;
            }
        }
        catch (ProofInputException e) {
        }

        return term;

    }

    ////////////////////////////////////////////////
    //////////////// GENERAL LOGIC /////////////////
    ////////////////  (Calculus) ///////////////////
    ////////////////////////////////////////////////

    /**
     * Deletes all formulae of the succedent / antecedent.
     * 
     * @param goal
     *            Goal to delete formulae from.
     * @param antec
     *            If true, antecedent formulae are deleted, else succedent
     *            formulae.
     */
    public static void clearSemisequent(Goal goal, boolean antec) {
        final Semisequent semiseq = antec ? goal.sequent().antecedent() : goal
                .sequent().succedent();
        for (final SequentFormula f : semiseq) {
            final PosInOccurrence gPio = new PosInOccurrence(f,
                    PosInTerm.getTopLevel(), antec);
            goal.removeFormula(gPio);
        }
    }

    /**
     * An equals method that, before the comparison, replaces all program
     * locations in the supplied arguments by their branch-unique versions.
     * 
     * @param se1
     *            First element to check equality (mod renaming) for.
     * @param se2
     *            Second element to check equality (mod renaming) for.
     * @param goal
     *            The goal of the current branch (for getting branch-unique
     *            names).
     * @param services
     *            The Services object.
     * @return true iff source elements can be matched, considering
     *         branch-unique location names.
     */
    public static boolean equalsModBranchUniqueRenaming(SourceElement se1,
            SourceElement se2, Node node, Services services) {

        // Quick short cut for the special case where no program variables
        // have to be renamed.
        if (se1.equalsModRenaming(se2, new NameAbstractionTable())) {
            return true;
        }

        LocVarReplBranchUniqueMap replMap = new LocVarReplBranchUniqueMap(node,
                DefaultImmutableSet.<LocationVariable> nil());

        ProgVarReplaceVisitor replVisitor1 = new ProgVarReplaceVisitor(
                (ProgramElement) se1, replMap, services);
        ProgVarReplaceVisitor replVisitor2 = new ProgVarReplaceVisitor(
                (ProgramElement) se2, replMap, services);

        replVisitor1.start();
        replVisitor2.start();

        return replVisitor1.result().equalsModRenaming(replVisitor2.result(),
                new NameAbstractionTable());
    }

    // /////////////////////////////////////////////////
    // //////////////// JOIN RELATED //////////////////
    // /////////////////////////////////////////////////

    /**
     * Creates a path condition that is equivalent to the disjunction of the two
     * supplied formulae, but possibly simpler. In the ideal case, the returned
     * formula can be literally shorter than each of the two formulae; in this
     * case, it consists of the common elements of those.
     * <p>
     * 
     * The underlying idea is based upon the observation that many path
     * conditions that should be joined are conjunctions of mostly the same
     * elements and, in addition, formulae phi and !phi that vanish after
     * creating the disjunction of the path conditions. The corresponding valid
     * formula is <code>(phi & psi) | (phi & !psi) <-> phi</code>
     * <p>
     * 
     * For formulae that cannot be simplified by this law, the method performs
     * two additional steps:<br>
     * (1) it applies, if possible, distributivity to simplify the result<br>
     * (2) it checks whether the disjunction is already equivalent to the common
     * parts of the formulae only. This often happens when merging all branches
     * that occur in symbolic execution.<br>
     * 
     * @param cond1
     *            First path condition to join.
     * @param cond2
     *            Second path condition to join.
     * @param services
     *            The services object.
     * @return A path condition that is equivalent to the disjunction of the two
     *         supplied formulae, but possibly simpler.
     */
    public static Term createSimplifiedDisjunctivePathCondition(
            final Term cond1, final Term cond2, Services services) {

        TermBuilder tb = services.getTermBuilder();

        ArrayList<Term> cond1ConjElems = getConjunctiveElementsFor(cond1);
        ArrayList<Term> cond2ConjElems = getConjunctiveElementsFor(cond2);

        final ArrayList<Term> fCond1ConjElems = new ArrayList<Term>(
                cond1ConjElems);
        final ArrayList<Term> fCond2ConjElems = new ArrayList<Term>(
                cond2ConjElems);

        if (cond1ConjElems.size() == cond2ConjElems.size()) {
            for (int i = 0; i < fCond1ConjElems.size(); i++) {
                Term elem1 = fCond1ConjElems.get(i);
                Term elem2 = fCond2ConjElems.get(i);

                if (!elem1.equals(elem2)) {
                    // Try to show that the different elements can be left
                    // out in the disjunction, since they are complementary
                    if (isProvableWithSplitting(tb.or(elem1, elem2), services)) {
                        cond1ConjElems.remove(elem1);
                        cond2ConjElems.remove(elem2);
                    }
                    else {
                        // Simplification is not applicable!
                        // Do a reset and leave the loop.
                        cond1ConjElems = fCond1ConjElems;
                        cond2ConjElems = fCond2ConjElems;

                        break;
                    }
                }
            }
        }

        Term result1 = joinConjuctiveElements(cond1ConjElems, services);
        Term result2 = joinConjuctiveElements(cond2ConjElems, services);

        Term result;

        if (result1.equals(result2)) {
            result = result1;
        }
        else {
            Option<Pair<Term, Term>> distinguishingAndEqual = getDistinguishingFormula(
                    result1, result2, services);
            
            if (!distinguishingAndEqual.isSome()) {
                distinguishingAndEqual = getDistinguishingFormula(
                        result2, result1, services);
            }
            
            assert distinguishingAndEqual instanceof Option.Some : "Possibly, this join is not sound!";
            
            ArrayList<Term> equalConjunctiveElems = getConjunctiveElementsFor(distinguishingAndEqual.getValue().second);

            // Apply distributivity to simplify the formula
            cond1ConjElems.removeAll(equalConjunctiveElems);
            cond2ConjElems.removeAll(equalConjunctiveElems);

            result1 = joinConjuctiveElements(cond1ConjElems, services);
            result2 = joinConjuctiveElements(cond2ConjElems, services);
            Term commonElemsTerm = joinConjuctiveElements(
                    equalConjunctiveElems, services);

            result = tb.and(tb.or(result1, result2), commonElemsTerm);

            // Last try: Check if the formula is equivalent to only the
            // common elements...
            Term equivalentToCommon = tb.and(tb.imp(result, commonElemsTerm),
                    tb.imp(commonElemsTerm, result));
            if (isProvableWithSplitting(equivalentToCommon, services)) {
                result = commonElemsTerm;
            }
        }

        return result;
    }

    /**
     * Computes a formula that implies pathCondition1 and, if pathCondition1 and
     * pathCondition2 are contradicting, does not imply pathCondition2. The
     * computed formula is at most as complex as pathCondition1. This so
     * generated distinguishing formula is returned in the first element of the
     * pair; the "rest" is contained in the second. It always holds that the
     * conjunction of the first element of the pair and the second element of
     * the pair is equivalent to pathCondition1.
     * 
     * @param pathCondition1
     *            The first formula to compute a distinguishing formula for.
     * @param pathCondition2
     *            The second formula to compute a distinguishing formula for.
     * @param services
     *            The services object.
     * @return (1) A formula that implies pathCondition1 and, if pathCondition1
     *         and pathCondition2 are contradicting, does not imply
     *         pathCondition2, and (2) the "rest" of pathCondition1 that is
     *         common with pathCondition2.
     */
    public static Option<Pair<Term, Term>> getDistinguishingFormula(
            Term pathCondition1, Term pathCondition2, Services services) {

        final TermWrapperFactory factory = new TermWrapperFactory();

        final LinkedHashSet<TermWrapper> cond1ConjElems = new LinkedHashSet<JoinRuleUtils.TermWrapper>();
        final LinkedHashSet<TermWrapper> cond2ConjElems = new LinkedHashSet<JoinRuleUtils.TermWrapper>();

        for (final Term term : getConjunctiveElementsFor(pathCondition1)) {
            cond1ConjElems.add(factory.wrapTerm(term));
        }

        for (final Term term : getConjunctiveElementsFor(pathCondition2)) {
            cond2ConjElems.add(factory.wrapTerm(term));
        }

        // The intersection of cond1ConjElems and cond2ConjElems
        final LinkedHashSet<TermWrapper> commonElements = new LinkedHashSet<JoinRuleUtils.TermWrapper>(
                cond1ConjElems);
        commonElements.retainAll(cond2ConjElems);

        // The remaining rest
        final LinkedHashSet<TermWrapper> distinguishingElements = new LinkedHashSet<JoinRuleUtils.TermWrapper>(
                cond1ConjElems);
        distinguishingElements.removeAll(commonElements);

        if (distinguishingElements.isEmpty() && !cond1ConjElems.isEmpty()) {
            return new Option.None<Pair<Term, Term>>();
        }

        return new Option.Some<Pair<Term, Term>>(
                new Pair<Term, Term>(
                        joinConjuctiveElements(TermWrapper.toTermList(
                                new ArrayList<Term>(), distinguishingElements),
                                services),
                        joinConjuctiveElements( TermWrapper.toTermList(
                                new ArrayList<Term>(), commonElements),
                                services)));

    }
    
    /**
     * Checks if two given path conditions are distinguishable.
     *
     * @param pathCondition1 First path condition to check.
     * @param pathCondition2 Second path condition to check.
     * @param services The services object.
     * @return True iff the two given path conditions are distinguishable.
     */
    public static boolean pathConditionsAreDistinguishable(Term pathCondition1,
            Term pathCondition2, Services services) {
        Option<Pair<Term, Term>> distinguishingAndEqualFormula1 = getDistinguishingFormula(
                pathCondition1, pathCondition2, services);
        Option<Pair<Term, Term>> distinguishingAndEqualFormula2 = getDistinguishingFormula(
                pathCondition2, pathCondition1, services);

        return distinguishingAndEqualFormula1.isSome()
                || distinguishingAndEqualFormula2.isSome();
    }

    /**
     * Closes the given partner goal, using the CloseAfterJoin rule.
     * 
     * @param joinNodeParent
     *            Parent of remaining join node.
     * @param joinPartner
     *            Partner goal to close.
     */
    public static void closeJoinPartnerGoal(Node joinNodeParent,
            Goal joinPartner, PosInOccurrence pio,
            SymbolicExecutionState joinState,
            SymbolicExecutionState joinPartnerState, Term pc) {

        InitConfig initConfig = joinNodeParent.proof().getInitConfig();

        CloseAfterJoin closeRule = CloseAfterJoin.INSTANCE;
        RuleApp app = closeRule.createApp(pio, joinPartner.node(),
                joinNodeParent, joinState, joinPartnerState, pc);

        // Register rule if not done yet.
        // This avoids error messages of the form
        // "no justification found for rule...".
        if (initConfig.getJustifInfo().getJustification(closeRule) == null) {
            initConfig.registerRuleIntroducedAtNode(app, joinPartner.node(),
                    true);
        }

        joinPartner.apply(app);
    }

    /**
     * Converts a sequent (given by goal & pos in occurrence) to an SE state
     * (U,C). Thereby, all program variables occurring in the symbolic state are
     * replaced by branch-unique correspondents in order to enable merging of
     * different branches declaring local variables.
     * <p>
     * 
     * @param goal
     *            Current goal.
     * @param pio
     *            Position of update-program counter formula in goal.
     * @param services
     *            The services object.
     * @return An SE state (U,C).
     * @see #sequentToSETriple(Goal, PosInOccurrence, Services)
     */
    public static SymbolicExecutionState sequentToSEPair(Node node,
            PosInOccurrence pio, Services services) {

        SymbolicExecutionStateWithProgCnt triple = sequentToSETriple(node, pio,
                services);

        return new SymbolicExecutionState(triple.first, triple.second, node);
    }

    /**
     * Converts a sequent (given by goal & pos in occurrence) to an SE state
     * (U,C,p). Thereby, all program variables occurring in the program counter
     * and in the symbolic state are replaced by branch-unique correspondents in
     * order to enable merging of different branches declaring local variables.
     * <p>
     * 
     * The problem which makes this renaming necessary is the fact that when
     * executing a program like <code>int x; x = ...</code>, the variable x is
     * renamed to x_1, x_2 and so on in different branches, which makes a
     * "normal" merging impossible. Branch unique names are tracked in the
     * LocationVariables when they are renamed in InnerVariableNamer. Soundness
     * is not effected by the switch to branch-unique names. However, merged
     * nodes are then of course potentially different from their predecessors
     * concerning the involved local variable symbols.
     * 
     * @param goal
     *            Current goal.
     * @param pio
     *            Position of update-program counter formula in goal.
     * @param services
     *            The services object.
     * @return An SE state (U,C,p).
     */
    public static SymbolicExecutionStateWithProgCnt sequentToSETriple(
            Node node, PosInOccurrence pio, Services services) {

        TermBuilder tb = services.getTermBuilder();

        ImmutableList<SequentFormula> pathConditionSet = ImmutableSLList.nil();
        pathConditionSet = pathConditionSet.prepend(node.sequent().antecedent()
                .asList());

        Term selected = pio.subTerm();

        for (SequentFormula sf : node.sequent().succedent()) {
            if (!sf.formula().equals(selected)) {
                pathConditionSet = pathConditionSet.prepend(new SequentFormula(
                        services.getTermBuilder().not(sf.formula())));
            }
        }

        Term updateTerm = null;
        ProgramElement programCounter = null;
        Term postCondition = null;
        Modality modality = null;

        Term termAfterUpdate = null;

        if (selected.op() instanceof UpdateApplication) {
            updateTerm = selected.sub(0);
            termAfterUpdate = selected.sub(1);
        }
        else {
            termAfterUpdate = selected;
        }

        if (termAfterUpdate.op() instanceof Modality) {
            programCounter = termAfterUpdate.javaBlock().program();
            postCondition = termAfterUpdate.sub(0);
            modality = (Modality) termAfterUpdate.op();
        }
        else {
            postCondition = termAfterUpdate;
        }

        // Note: We may not rename variables in the program counter that also
        // occur in the post condition. Otherwise, we may render the goal
        // unprovable.

        LocVarReplBranchUniqueMap replMap = new LocVarReplBranchUniqueMap(
                node, getLocationVariables(postCondition, services));

        // Replace location variables in program counter by their
        // branch-unique versions
        Term progCntAndPostCond = null;
        if (programCounter != null) {

            ProgVarReplaceVisitor replVisitor = new ProgVarReplaceVisitor(
                    programCounter, replMap, services);
            replVisitor.start();
            programCounter = replVisitor.result();
            progCntAndPostCond = services.getTermBuilder().prog(modality,
                    JavaBlock.createJavaBlock((StatementBlock) programCounter),
                    postCondition);
        }
        else {
            progCntAndPostCond = postCondition;
        }

        // Replace location variables in update by branch-unique versions
        ImmutableList<Term> newElementaries = ImmutableSLList.nil();

        if (updateTerm != null) {
            LinkedList<Term> elementaries = getElementaryUpdates(selected
                    .sub(0));
            for (Term elementary : elementaries) {
                ElementaryUpdate upd = (ElementaryUpdate) elementary.op();
                LocationVariable lhs = (LocationVariable) upd.lhs();

                newElementaries = newElementaries.prepend(tb.elementary(
                        (LocationVariable) (replMap.get(lhs)),
                        elementary.sub(0)));
            }
        }

        return new SymbolicExecutionStateWithProgCnt(
                tb.parallel(newElementaries), // Update
                joinListToAndTerm(pathConditionSet, services), // Path Condition
                progCntAndPostCond, // Program Counter and Post Condition
                node); // CorrespondingNode
    }

    // /////////////////////////////////////////////////
    // /////////////////// PRIVATE /////////////////////
    // /////////////////////////////////////////////////

    /**
     * Anonymizes all program variables occurring in the given term. If x is a
     * PV in the term, the result will be of the form
     * <code>{ ... || x := vx || ...} term</code> where vx is a fresh variable.
     * Returns all free variables of the new termin the second component of the
     * pair.
     * 
     * @param term
     *            Term to anonymize.
     * @param services
     *            The services object.
     * @return A term of the form <code>{ ... || x := vx || ...} term</code> for
     *         every PV x occurring in the term, where vx is a fresh variable.
     */
    private static Pair<Term, ImmutableSet<QuantifiableVariable>> anonymizeProgramVariables(
            final Term term, final Services services) {
        TermBuilder tb = services.getTermBuilder();

        ImmutableSet<QuantifiableVariable> freeVars = term.freeVars();
        ImmutableList<Term> elementaries = ImmutableSLList.nil();

        for (LocationVariable loc : getLocationVariables(term, services)) {
            final String newName = tb
                    .newName(stripIndex(loc.name().toString()));
            final LogicVariable newVar = new LogicVariable(new Name(newName),
                    loc.sort());
            services.getNamespaces().variables().add(newVar);

            freeVars = freeVars.add(newVar);

            elementaries = elementaries.prepend(tb.elementary(tb.var(loc),
                    tb.var(newVar)));
        }

        return new Pair<Term, ImmutableSet<QuantifiableVariable>>(tb.apply(
                tb.parallel(elementaries), term), freeVars);
    }

    /**
     * Joins a list of sequent formulae to an and-connected term.
     * 
     * @param formulae
     *            Formulae to join.
     * @param services
     *            The services object.
     * @return And-formula connecting the given terms.
     */
    private static Term joinListToAndTerm(
            ImmutableList<SequentFormula> formulae, Services services) {
        if (formulae.size() == 0) {
            return services.getTermBuilder().tt();
        }
        else if (formulae.size() == 1) {
            return formulae.head().formula();
        }
        else {
            return services.getTermBuilder().and(formulae.head().formula(),
                    joinListToAndTerm(formulae.tail(), services));
        }
    }

    /**
     * Returns all elementary updates of a parallel update.
     * 
     * @param u
     *            Parallel update to get elementary updates from.
     * @return Elementary updates of the supplied parallel update.
     */
    private static LinkedList<Term> getElementaryUpdates(Term u) {
        LinkedList<Term> result = new LinkedList<Term>();

        if (u.op() instanceof ElementaryUpdate) {
            result.add(u);
        }
        else if (u.op() instanceof UpdateJunctor) {
            for (Term sub : u.subs()) {
                result.addAll(getElementaryUpdates(sub));
            }
        }
        else {
            throw new IllegalArgumentException("Expected an update!");
        }

        return result;
    }

    /**
     * Returns all used program locations in the given term. The term must be of
     * the form \<{ ... }\> phi (or \[{ ... }\] phi).
     * 
     * @param programCounterTerm
     *            The term (program counter) to extract locations from.
     * @param services
     *            The Services object.
     * @return The set of contained program locations.
     */
    private static ImmutableSet<LocationVariable> getProgramLocations(
            Term programCounterTerm, Services services) {
        CollectLocationVariablesVisitor visitor = new CollectLocationVariablesVisitor(
                programCounterTerm.javaBlock().program(), true, services);

        ImmutableSet<LocationVariable> progVars = DefaultImmutableSet.nil();

        // Collect program variables in Java block
        visitor.start();
        progVars = progVars.union(visitor.getLocationVariables());

        return progVars;
    }

    /**
     * Joins a list of formulae to a conjunction.
     * 
     * @param elems
     *            Formulae to join.
     * @param services
     *            The services object.
     * @return A conjunction of the supplied formulae.
     */
    private static Term joinConjuctiveElements(final List<Term> elems,
            Services services) {
        TermBuilder tb = services.getTermBuilder();

        if (elems.isEmpty()) {
            return tb.tt();
        }

        Term result = elems.get(0);
        for (int i = 1; i < elems.size(); i++) {
            Term term = elems.get(i);
            result = tb.and(result, term);
        }

        return result;
    }

    /**
     * Tries to prove the given formula and returns the result.
     * 
     * @param toProve
     *            Formula to prove.
     * @param services
     *            The services object.
     * @param doSplit
     *            if true, splitting is allowed (normal mode).
     * @return The proof result.
     */
    private static ApplyStrategyInfo tryToProve(Term toProve,
            Services services, boolean doSplit, String sideProofName) {
        final ProofEnvironment sideProofEnv = SideProofUtil
                .cloneProofEnvironmentWithOwnOneStepSimplifier(
                        services.getProof(), // Parent Proof
                        new Choice[] {}); // useSimplifyTermProfile

        ApplyStrategyInfo proofResult = null;
        try {
            ProofStarter proofStarter = SideProofUtil
                    .createSideProof(
                            sideProofEnv, // Proof environment
                            Sequent.createSequent(
                                    // Sequent to prove
                                    Semisequent.EMPTY_SEMISEQUENT,
                                    new Semisequent(new SequentFormula(toProve))),
                                    sideProofName); // Proof name

            proofResult = proofStarter.start();
        }
        catch (ProofInputException e) {
        }

        return proofResult;
    }

    /**
     * Tries to prove the given formula and returns whether the prove could be
     * closed.
     * 
     * @param toProve
     *            Formula to prove.
     * @param services
     *            The services object.
     * @param doSplit
     *            if true, splitting is allowed (normal mode).
     * @return True iff the given formula has been successfully proven.
     */
    private static boolean isProvable(Term toProve, Services services,
            boolean doSplit) {

        ApplyStrategyInfo proofResult = tryToProve(toProve, services, doSplit, "Provability check");
        boolean result = proofResult.getProof().closed();

        return result;

    }

    /**
     * Simplifies the given {@link Term} in a side proof with splits. This code
     * has been copied from {@link SymbolicExecutionUtil} and only been slightly
     * modified (to allow for splitting the proof).
     * 
     * @param parentProof
     *            The parent {@link Proof}.
     * @param term
     *            The {@link Term} to simplify.
     * @return The simplified {@link Term}.
     * @throws ProofInputException
     *             Occurred Exception.
     * 
     * @see SymbolicExecutionUtil#simplify(Proof, Term)
     */
    private static Term simplify(Proof parentProof, Term term)
            throws ProofInputException {

        final Services services = parentProof.getServices();

        final ApplyStrategyInfo info = tryToProve(term, services, true, "Term simplification");

        // The simplified formula is the conjunction of all open goals
        ImmutableList<Goal> openGoals = info.getProof().openEnabledGoals();
        final TermBuilder tb = services.getTermBuilder();
        if (openGoals.isEmpty()) {
            return tb.tt();
        }
        else {
            ImmutableList<Term> goalImplications = ImmutableSLList.nil();
            for (Goal goal : openGoals) {
                Term goalImplication = sequentToFormula(goal.sequent(),
                        services);
                goalImplications = goalImplications.append(goalImplication);
            }

            return tb.and(goalImplications);
        }
    }

    /**
     * Converts a Sequent "Gamma ==> Delta" into a single formula equivalent to
     * "/\ Gamma -> \/ Delta"; however, the formulae in Gamma are shifted to the
     * succedent by the negation-left rule, so the result of this method is a
     * disjunction, not an implication.
     * 
     * @param sequent
     *            The sequent to convert to a formula.
     * @param services
     *            The services object.
     * @return A formula equivalent to the given sequent.
     */
    private static Term sequentToFormula(Sequent sequent, Services services) {
        TermBuilder tb = services.getTermBuilder();

        ImmutableList<Term> negAntecedentForms = ImmutableSLList.nil();
        ImmutableList<Term> succedentForms = ImmutableSLList.nil();

        // Shift antecedent formulae to the succedent by negation
        for (SequentFormula sf : sequent.antecedent().asList()) {
            negAntecedentForms = negAntecedentForms
                    .prepend(tb.not(sf.formula()));
        }

        for (SequentFormula sf : sequent.succedent().asList()) {
            succedentForms = succedentForms.prepend(sf.formula());
        }

        return tb.or(negAntecedentForms.prepend(succedentForms));
    }

    /**
     * Tells whether a name is unique in the passed list of global variables.
     * 
     * @param name
     *            The name to check uniqueness for.
     * @param globals
     *            The global variables for the givan branch.
     * @see VariableNamer#isUniqueInGlobals(String, Globals)
     */
    private static boolean isUniqueInGlobals(String name,
            ImmutableSet<ProgramVariable> globals) {
        for (final ProgramVariable n : globals) {
            if (n.toString().equals(name)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Looks up a program variable by its name in the PV namespace.
     * 
     * @param name
     *            Name to find a PV for.
     * @return The PV with the given name in the global namespace, or null if
     *         there is none.
     */
    private static LocationVariable lookupVarInNS(String name, Services services) {
        return (LocationVariable) services.getNamespaces().programVariables()
                .lookup(new Name(name));
    }
    
    /**
     * Creates {@link TermWrapper} objects, thereby ensuring
     * that equal term wrappers also have equal hash codes.
     *
     * @author Dominic Scheurer
     */
    static class TermWrapperFactory {
        private ArrayList<Term> wrappedTerms = new ArrayList<Term>();
        
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
     * Simple term wrapper for comparing terms modulo renaming.
     *
     * @author Dominic Scheurer
     * @see TermWrapperFactory
     */
    static class TermWrapper {
        private Term term;
        private int hashcode;
        
        public TermWrapper(Term term, int hashcode) {
            this.term = term;
            this.hashcode = hashcode;
        }
        
        public Term getTerm() {
            return term;
        }
        
        @Override
        public boolean equals(Object obj) {
            return obj instanceof TermWrapper &&
                    term.equalsModRenaming(((TermWrapper) obj).getTerm());
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
         * Adds the wrapped content of the Iterable object into the given target
         * collection.
         *
         * @param target
         *            The collection to insert the wrapped terms into.
         * @param wrappedCollection
         *            Iterable to transform.
         * @return The target collection with inserted terms.
         */
        public static <T extends Collection<Term>> T toTermList(T target,
                Iterable<TermWrapper> wrappedCollection) {
            Iterator<TermWrapper> it = wrappedCollection.iterator();

            while (it.hasNext()) {
                target.add(it.next().getTerm());
            }
            
            return target;
        }
    }
    
    /**
     * A simple Scala-like option type: Either Some(value) or None.
     *
     * @author Dominic Scheurer
     *
     * @param <T> Type for the content of the option.
     */
    public static abstract class Option<T> {
        static class Some<T> extends Option<T> {
            private T value;
            
            public Some(T value) {
                this.value = value;
            }
            
            public T getValue() {
                return value;
            }
        }
        
        static class None<T> extends Option<T> {}
        
        public boolean isSome() {
            return this instanceof Some;
        }
        
        /**
         * Returns the value of this object if is a Some; otherwise,
         * an exception is thrown.
         *
         * @return The value of this object.
         * @throws IllegalAccessError If this object is a None.
         */
        public T getValue() {
            if (isSome()) {
                return ((Some<T>) this).getValue();
            }
            else {
                throw new IllegalAccessError("Cannot otain a value from a None object.");
            }
        }
    }

    /**
     * Visitor for collecting program locations in a Java block.
     * 
     * @author Dominic Scheurer
     */
    private static class CollectLocationVariablesVisitor extends
            CreatingASTVisitor {
        private ImmutableSet<LocationVariable> variables = DefaultImmutableSet
                .nil();

        public CollectLocationVariablesVisitor(ProgramElement root,
                boolean preservesPos, Services services) {
            super(root, preservesPos, services);
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
     * Map for renaming variables to their branch-unique names. Putting things
     * into this map has absolutely no effect; the get method just relies on the
     * {@link LocationVariable#getBranchUniqueName()} method of the respective
     * location variable. Therefore, this map is also a singleton object.
     * 
     * @author Dominic Scheurer
     */
    private static class LocVarReplBranchUniqueMap extends
            HashMap<ProgramVariable, ProgramVariable> {
        private static final long serialVersionUID = 2305410114265133879L;

        private final Node node;
        private final ImmutableSet<LocationVariable> doNotRename;
        private final HashMap<LocationVariable, ProgramVariable> cache =
                new HashMap<LocationVariable, ProgramVariable>();

        public LocVarReplBranchUniqueMap(Node goal,
                ImmutableSet<LocationVariable> doNotRename) {
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
            }
            else {
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
}
