/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation;



import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.Sequent;
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

        public JTerm getDefaultValue(TermServices services) {
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
    private JTerm translateReplaceAndAddTerm(TacletGoalTemplate template, JTerm find,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();
        JTerm replace = find;
        if (template instanceof RewriteTacletGoalTemplate) {
            replace = ((RewriteTacletGoalTemplate) template).replaceWith();
        }
        JTerm add = template.sequent() != null ? translate(template.sequent(), services)
                : TacletSections.ADD.getDefaultValue(services);
        if (add == null) {
            add = TacletSections.ADD.getDefaultValue(services);
        }
        if (replace == null) {
            replace = TacletSections.REPLACE.getDefaultValue(services);
        }

        return tb.imp(tb.equals(find, replace), add);
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
    private JTerm translateReplaceAndAddFormula(TacletGoalTemplate template, JTerm find,
            int polarity,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();

        JTerm replace = find;
        if (template instanceof RewriteTacletGoalTemplate) {
            replace = ((RewriteTacletGoalTemplate) template).replaceWith();
        }

        JTerm add = template.sequent() != null ? translate(template.sequent(), services)
                : TacletSections.ADD.getDefaultValue(services);
        if (add == null) {
            add = TacletSections.ADD.getDefaultValue(services);
        }
        if (replace == null) {
            replace = TacletSections.REPLACE.getDefaultValue(services);
        }

        assert polarity == 0 || add == TacletSections.ADD.getDefaultValue(services)
                : "add() commands not allowed in polarity rules (syntactically forbidden)";

        return tb.imp(translateEquivalence(find, replace, polarity, services), add);

    }

    private JTerm translateEquivalence(JTerm find, JTerm replace, int polarity,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();
        return switch (polarity) {
            case 0 -> tb.equals(find, replace);
            case 1 -> tb.imp(replace, find);
            case -1 -> tb.imp(find, replace);
            default -> throw new IllegalArgumentException();
        };
    }

    private JTerm translateReplaceAndAddSequent(TacletGoalTemplate template, int type,
            TermServices services) {
        TermBuilder tb = services.getTermBuilder();
        Sequent replace = null;
        if (template instanceof AntecSuccTacletGoalTemplate) {
            replace = ((AntecSuccTacletGoalTemplate) template).replaceWith();
        }

        JTerm add = template.sequent() != null ? translate(template.sequent(), services)
                : TacletSections.ADD.getDefaultValue(services);
        JTerm rep = replace == null ? TacletSections.REPLACE.getDefaultValue(services)
                : translate(replace, services);
        if (add == null) {
            add = TacletSections.ADD.getDefaultValue(services);
        }
        if (rep == null) {
            rep = TacletSections.REPLACE.getDefaultValue(services);
        }
        return tb.or(rep, add);
    }

    /**
     * Translates a RewriteTaclet to a formula.
     */
    @Override
    public JTerm translate(Taclet taclet, TermServices services) throws IllegalTacletException {


        TermBuilder tb = services.getTermBuilder();

        // the standard translation of the patterns.

        JTerm find = TacletSections.FIND.getDefaultValue(services),
                assum = TacletSections.ASSUM.getDefaultValue(services);

        // translate the find pattern.
        if (taclet instanceof FindTaclet findTaclet) {
            if (getFindFromTaclet(findTaclet) != null) {
                find = getFindFromTaclet(findTaclet);
            }
        }

        // translate the replace and add patterns of the taclet.
        ImmutableList<JTerm> list = ImmutableSLList.nil();

        for (TacletGoalTemplate template : taclet.goalTemplates()) {

            if (taclet instanceof AntecTaclet) {
                list = list.append(translateReplaceAndAddSequent(template, ANTE, services));

            } else if (taclet instanceof SuccTaclet) {
                list = list.append(translateReplaceAndAddSequent(template, SUCC, services));

            } else if (taclet instanceof RewriteTaclet rwTaclet) {
                if (rwTaclet.find().sort().equals(JavaDLTheory.FORMULA)) {
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
        if (taclet.assumesSequent() != null) {
            if ((assum = translate(taclet.assumesSequent(), services)) == null) {
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
     * <p>
     * Originally, this simply calls {@link FindTaclet#find()}. Overriding classes may choose to
     * garnish the result with additional information.
     *
     * @param findTaclet a non-null taclet instance
     * @return the find clause of the argument
     */
    protected JTerm getFindFromTaclet(FindTaclet findTaclet) {
        return findTaclet.find();
    }

    private int getPolarity(RewriteTaclet rwTaclet) {
        var restr = rwTaclet.applicationRestriction();
        if (restr.matches(ApplicationRestriction.ANTECEDENT_POLARITY)) {
            return -1;
        } else if (restr.matches(ApplicationRestriction.SUCCEDENT_POLARITY)) {
            return +1;
        } else {
            return 0;
        }
    }
}
