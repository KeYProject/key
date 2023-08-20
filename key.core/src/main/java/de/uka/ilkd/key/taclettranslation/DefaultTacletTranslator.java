/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation;



import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Translates a rewrite taclet to a formula.
 *
 *
 */
public class DefaultTacletTranslator extends AbstractSkeletonGenerator {


    static private final int ANTE = 0;
    static private final int SUCC = 1;


    private enum TacletSections {
        REPLACE, ADD, ASSUM, FIND;

        public Term getDefaultValue(TermServices services) {
            return services.getTermBuilder().ff();
        }
    }


    /**
     * Translates the replace and add pattern of a goal template to: find=replace->add <br>
     * Use this method if you want to translate a taclet, where the find pattern is a term.
     *
     * @param template contains the replace and add pattern that are to be translated.
     * @param find the find pattern of the taclet, already translated.
     * @param services TODO
     * @return translation
     */
    private Term translateReplaceAndAddTerm(TacletGoalTemplate template, Term find,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();
        Term replace = find;
        if (template instanceof RewriteTacletGoalTemplate) {
            replace = ((RewriteTacletGoalTemplate) template).replaceWith();
        }
        Term add = template.sequent() != null ? translate(template.sequent(), services)
                : TacletSections.ADD.getDefaultValue(services);
        if (add == null) {
            add = TacletSections.ADD.getDefaultValue(services);
        }
        if (replace == null) {
            replace = TacletSections.REPLACE.getDefaultValue(services);
        }

        Term term = tb.imp(tb.equals(find, replace), add);
        return term;
    }

    /**
     * Translates the replace and add pattern of a goal template to: (find<->replace)->add<br>
     * Use this method if you want to translate a taclet, where the find pattern is a formula.
     *
     * @param template contains the replace and add pattern that are to be translated.
     * @param find the find pattern of the taclet, already translated.
     * @param polarity a value between -1 and 1. describes the expected polarity of the find clause
     *        (-1 antecedent, 0 both, +1 succedent)
     * @param services TODO
     * @return translation
     */
    private Term translateReplaceAndAddFormula(TacletGoalTemplate template, Term find, int polarity,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();

        Term replace = find;
        if (template instanceof RewriteTacletGoalTemplate) {
            replace = ((RewriteTacletGoalTemplate) template).replaceWith();
        }

        Term add = template.sequent() != null ? translate(template.sequent(), services)
                : TacletSections.ADD.getDefaultValue(services);
        if (add == null) {
            add = TacletSections.ADD.getDefaultValue(services);
        }
        if (replace == null) {
            replace = TacletSections.REPLACE.getDefaultValue(services);
        }

        assert polarity == 0 || add == TacletSections.ADD.getDefaultValue(services)
                : "add() commands not allowed in polarity rules (syntactically forbidden)";

        Term term = tb.imp(translateEquivalence(find, replace, polarity, services), add);
        return term;

    }

    private Term translateEquivalence(Term find, Term replace, int polarity,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();
        switch (polarity) {
        case 0:
            return tb.equals(find, replace);
        case 1:
            return tb.imp(replace, find);
        case -1:
            return tb.imp(find, replace);
        default:
            throw new IllegalArgumentException();
        }
    }

    private Term translateReplaceAndAddSequent(TacletGoalTemplate template, int type,
            TermServices services) {

        TermBuilder tb = services.getTermBuilder();
        Sequent replace = null;
        if (template instanceof AntecSuccTacletGoalTemplate) {
            replace = ((AntecSuccTacletGoalTemplate) template).replaceWith();
        }

        Term add = template.sequent() != null ? translate(template.sequent(), services)
                : TacletSections.ADD.getDefaultValue(services);
        Term rep = replace == null ? TacletSections.REPLACE.getDefaultValue(services)
                : translate(replace, services);
        if (add == null) {
            add = TacletSections.ADD.getDefaultValue(services);
        }
        if (rep == null) {
            rep = TacletSections.REPLACE.getDefaultValue(services);
        }
        Term term = tb.or(rep, add);
        return term;
    }

    /**
     * Translates a RewriteTaclet to a formula.
     */
    @Override
    public Term translate(Taclet taclet, TermServices services) throws IllegalTacletException {


        TermBuilder tb = services.getTermBuilder();

        // the standard translation of the patterns.

        Term find = TacletSections.FIND.getDefaultValue(services),
                assum = TacletSections.ASSUM.getDefaultValue(services);

        // translate the find pattern.
        if (taclet instanceof FindTaclet) {
            FindTaclet findTaclet = (FindTaclet) taclet;
            if (getFindFromTaclet(findTaclet) != null) {
                find = getFindFromTaclet(findTaclet);
            }
        }

        // translate the replace and add patterns of the taclet.
        ImmutableList<Term> list = ImmutableSLList.nil();

        for (TacletGoalTemplate template : taclet.goalTemplates()) {

            if (taclet instanceof AntecTaclet) {
                list = list.append(translateReplaceAndAddSequent(template, ANTE, services));

            } else if (taclet instanceof SuccTaclet) {
                list = list.append(translateReplaceAndAddSequent(template, SUCC, services));

            } else if (taclet instanceof RewriteTaclet) {
                RewriteTaclet rwTaclet = (RewriteTaclet) taclet;
                if (rwTaclet.find().sort().equals(Sort.FORMULA)) {
                    int polarity = getPolarity(rwTaclet);
                    list = list.append(
                        translateReplaceAndAddFormula(template, find, polarity, services));

                } else {
                    list = list.append(translateReplaceAndAddTerm(template, find, services));

                }
            } else if (taclet instanceof NoFindTaclet) {
                list = list.append(translateReplaceAndAddSequent(template, SUCC, services));
            } else {
                throw new IllegalTacletException(
                    "Not AntecTaclet, not SuccTaclet, not RewriteTaclet, not NoFindTaclet");
            }
        }
        if (taclet.ifSequent() != null) {
            if ((assum = translate(taclet.ifSequent(), services)) == null) {
                assum = TacletSections.ASSUM.getDefaultValue(services);
            }
        }


        if (taclet instanceof AntecTaclet || taclet instanceof SuccTaclet) {
            if (taclet instanceof AntecTaclet) {
                find = tb.not(find);
            }
            return tb.imp(tb.and(list), tb.or(find, assum));
        }
        return tb.imp(tb.and(list), assum);
    }

    /**
     * Retrieve the "find" Term from a FindTaclet.
     *
     * Originally, this simply calls {@link FindTaclet#find()}. Overriding classes may choose to
     * garnish the result with additional information.
     *
     * @param findTaclet a non-null taclet instance
     * @return the find clause of the argument
     */
    protected Term getFindFromTaclet(FindTaclet findTaclet) {
        return findTaclet.find();
    }

    private int getPolarity(RewriteTaclet rwTaclet) {
        int restr = rwTaclet.getApplicationRestriction();
        if ((restr & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
            return -1;
        } else if ((restr & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
            return +1;
        } else {
            return 0;
        }
    }
}
