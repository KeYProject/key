/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match;

import java.util.HashMap;
import java.util.Iterator;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.logic.op.UpdateApplication;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.*;
import org.key_project.util.collection.*;

import static org.key_project.rusty.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;


public class VMTacletMatcher implements TacletMatcher {
    /** the matcher for the find expression of the taclet */
    private final TacletMatchProgram findMatchProgram;
    /** the matcher for the taclet's assumes formulas */
    private final HashMap<Term, TacletMatchProgram> assumesMatchPrograms = new HashMap<>();

    /**
     * the variable conditions of the taclet that need to be satisfied by found schema variable
     * instantiations
     */
    private final ImmutableList<VariableCondition> varconditions;
    /** the built-in notFreeIn variable conditions */
    private final ImmutableList<NotFreeIn> varsNotFreeIn;

    /** the assumes sequent of the taclet */
    private final Sequent assumesSequent;
    /** the bound variables */
    private final ImmutableSet<QuantifiableVariable> boundVars;

    /**
     * flag indicating if preceding updates of the term to be matched should be ignored this
     * requires the taclet to ignore updates and that the find term does not start with an
     * {@link UpdateApplication} operator
     */
    private final boolean ignoreTopLevelUpdates;
    /**
     * the find expression of the taclet of {@code null} if it is a {@link NoFindTaclet}
     */
    private final Term findExp;

    public VMTacletMatcher(Taclet taclet) {
        varconditions = taclet.getVariableConditions();
        assumesSequent = taclet.ifSequent();
        boundVars = taclet.getBoundVariables();
        varsNotFreeIn = taclet.varsNotFreeIn();

        if (taclet instanceof FindTaclet ft) {
            findExp = ft.find();
            ignoreTopLevelUpdates = ft.ignoreTopLevelUpdates()
                    && !(findExp.op() instanceof UpdateApplication);
            findMatchProgram = TacletMatchProgram.createProgram(findExp);

        } else {
            ignoreTopLevelUpdates = false;
            findExp = null;
            findMatchProgram = TacletMatchProgram.EMPTY_PROGRAM;
        }

        for (SequentFormula sf : assumesSequent) {
            assumesMatchPrograms.put(sf.formula(), TacletMatchProgram.createProgram(sf.formula()));
        }
    }

    @Override
    public MatchConditions matchFind(Term term, MatchConditions matchCond, Services services) {
        if (findMatchProgram != TacletMatchProgram.EMPTY_PROGRAM) {
            if (ignoreTopLevelUpdates) {
                Pair</* term below updates */Term, MatchConditions> resultUpdateMatch =
                    matchAndIgnoreUpdatePrefix(term, matchCond);
                term = resultUpdateMatch.first;
                matchCond = resultUpdateMatch.second;
            }
            matchCond =
                checkConditions(findMatchProgram.match(term, matchCond, services), services);
        } else {
            matchCond = null;
        }

        return matchCond;
    }

    /**
     * {@inheritDoc}
     */
    public final MatchConditions checkConditions(MatchConditions cond, Services services) {
        MatchConditions result = cond;
        if (result != null) {
            final Iterator<SchemaVariable> svIterator = cond.getInstantiations().svIterator();

            if (!svIterator.hasNext()) {
                return checkVariableConditions(null, null, cond, services);// XXX
            }

            while (result != null && svIterator.hasNext()) {
                final SchemaVariable sv = svIterator.next();
                final Object o = result.getInstantiations().getInstantiation(sv);
                if (o instanceof SyntaxElement) {
                    result = checkVariableConditions(sv, (SyntaxElement) o, result, services);
                }
            }
        }

        return result;
    }

    /**
     * returns true iff the given variable is bound either in the ifSequent or in any part of the
     * TacletGoalTemplates
     *
     * @param v the bound variable to be searched
     */
    private boolean varIsBound(SchemaVariable v) {
        return (v instanceof QuantifiableVariable) && boundVars.contains((QuantifiableVariable) v);
    }

    /**
     * looks if a variable is declared as not free in
     *
     * @param var the SchemaVariable to look for
     * @return true iff declared not free
     */
    private boolean varDeclaredNotFree(SchemaVariable var) {
        for (final NotFreeIn nfi : varsNotFreeIn) {
            if (nfi.first() == var) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions checkVariableConditions(SchemaVariable var,
            SyntaxElement instantiationCandidate, MatchConditions matchCond, Services services) {
        if (matchCond != null) {
            if (instantiationCandidate instanceof Term term) {
                if (!(term.op() instanceof QuantifiableVariable)) {
                    if (varIsBound(var) || varDeclaredNotFree(var)) {
                        // match(x) is not a variable, but the corresponding template variable is
                        // bound
                        // or declared non free (so it has to be matched to a variable)
                        return null; // FAILED
                    }
                }
            }
            // check generic conditions
            for (final VariableCondition vc : varconditions) {
                matchCond = vc.check(var, instantiationCandidate, matchCond, services);
                if (matchCond == null) {
                    return null; // FAILED
                }
            }
        }
        return matchCond;
    }

    /**
     * ignores a possible update prefix This method assumes that the taclet allows to ignore updates
     * and the find expression does not start with an update application operator
     *
     * @param term the term to be matched
     * @param matchCond the accumulated match conditions for a successful match
     * @return a pair of updated match conditions and the unwrapped term without the ignored updates
     *         (Which have been added to the update context in the match conditions)
     */
    private Pair<Term, MatchConditions> matchAndIgnoreUpdatePrefix(final Term term,
            MatchConditions matchCond) {

        final Operator sourceOp = term.op();

        if (sourceOp instanceof UpdateApplication) {
            // updates can be ignored
            Term update = UpdateApplication.getUpdate(term);
            matchCond = matchCond.setInstantiations(
                matchCond.getInstantiations().addUpdate(update));
            return matchAndIgnoreUpdatePrefix(UpdateApplication.getTarget(term), matchCond);
        } else {
            return new Pair<>(term, matchCond);
        }
    }

    @Override
    public final IfMatchResult matchIf(Iterable<IfFormulaInstantiation> toMatch,
            Term template, MatchConditions matchCond, Services services) {
        TacletMatchProgram prg = assumesMatchPrograms.get(template);


        ImmutableList<IfFormulaInstantiation> resFormulas =
            ImmutableSLList.nil();
        ImmutableList<MatchConditions> resMC = ImmutableSLList.nil();

        final boolean updateContextPresent =
            !matchCond.getInstantiations().getUpdateContext().isEmpty();
        ImmutableList<Term> context =
            ImmutableSLList.nil();

        if (updateContextPresent) {
            context = matchCond.getInstantiations().getUpdateContext();
        }

        for (var cf : toMatch) {
            Term formula = cf.getConstrainedFormula().formula();

            if (updateContextPresent) {
                formula = matchUpdateContext(context, formula);
            }
            if (formula != null) {// update context not present or update context match succeeded
                final MatchConditions newMC =
                    checkConditions(prg.match(formula, matchCond, services), services);

                if (newMC != null) {
                    resFormulas = resFormulas.prepend(cf);
                    resMC = resMC.prepend(newMC);
                }
            }
        }
        return new IfMatchResult(resFormulas, resMC);
    }

    /**
     * the formula ensures that the update context described the update of the given formula.
     * If it does not then {@code null} is returned, otherwise the formula without the update
     * context.
     *
     * @param context the list of update label pairs describing the update context
     * @param formula the formula whose own update context must be equal (modulo renaming) to the
     *        given one
     * @return {@code null} if the update context does not match the one of the formula or the
     *         formula without the update context
     */
    private Term matchUpdateContext(ImmutableList<Term> context, Term formula) {
        ImmutableList<Term> curContext = context;
        for (int i = 0, size = context.size(); i < size; i++) {
            if (formula.op() instanceof UpdateApplication) {
                final Term update = UpdateApplication.getUpdate(formula);
                final Term u = curContext.head();
                if (RENAMING_TERM_PROPERTY.equalsModThisProperty(u, update)) {
                    curContext = curContext.tail();
                    formula = UpdateApplication.getTarget(formula);
                    continue;
                }
            }
            // update context does not match update prefix of formula
            return null;
        }
        return formula;
    }

    /**
     * @inheritDoc
     */
    @Override
    public final MatchConditions matchIf(Iterable<IfFormulaInstantiation> p_toMatch,
            MatchConditions p_matchCond, Services p_services) {

        final Iterator<SequentFormula> anteIterator = assumesSequent.antecedent().iterator();
        final Iterator<SequentFormula> succIterator = assumesSequent.succedent().iterator();

        ImmutableList<MatchConditions> newMC;

        for (final IfFormulaInstantiation candidateInst : p_toMatch) {
            // Part of fix for #1716: match antecedent with antecedent, succ with succ
            boolean candidateInAntec = (candidateInst instanceof IfFormulaInstSeq)
                    // Only IfFormulaInstSeq has inAntec() property ...
                    && (((IfFormulaInstSeq) candidateInst).inAntec())
                    || !(candidateInst instanceof IfFormulaInstSeq)
                            // ... and it seems we don't need the check for other implementations.
                            // Default: just take the next ante formula, else succ formula
                            && anteIterator.hasNext();

            Iterator<SequentFormula> itIfSequent = candidateInAntec ? anteIterator : succIterator;
            // Fix end

            assert itIfSequent.hasNext()
                    : "toMatch and assumes sequent must have same number of elements";
            newMC = matchIf(ImmutableSLList.<IfFormulaInstantiation>nil().prepend(candidateInst),
                itIfSequent.next().formula(), p_matchCond, p_services).getMatchConditions();

            if (newMC.isEmpty()) {
                return null;
            }

            p_matchCond = newMC.head();
        }
        assert !anteIterator.hasNext() && !succIterator.hasNext()
                : "toMatch and assumes sequent must have same number of elements";

        return p_matchCond;
    }
}
