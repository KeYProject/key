/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;

/**
 * Toy lemma generator used to evaluate the taclet-generating transformer approach: for a sum of
 * two integer literals it produces the ground rewrite taclet {@code \find(i + j) \replacewith(k)}
 * with {@code k} the literal denoting the sum.
 *
 * <p>
 * This covers the same ground as the system taclet {@code add_literals}, whose right-hand side is
 * computed by the metaconstruct {@code #add} at application time and is therefore neither
 * inspectable nor amenable to a soundness proof obligation. The taclets produced here are
 * metaconstruct-free, so the standard lemma machinery applies. The system taclet remains in the
 * rule base untouched; in particular it serves as the ground truth for discharging the generated
 * proof obligations.
 */
@NullMarked
public final class AddLiteralsLemmaGenerator implements LemmaTacletGenerator {

    public static final AddLiteralsLemmaGenerator INSTANCE = new AddLiteralsLemmaGenerator();

    private static final Name NAME = new Name("addLitLemma");

    private AddLiteralsLemmaGenerator() {
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        final IntegerLDT integerLDT =
            goal.proof().getServices().getTypeConverter().getIntegerLDT();
        final Term term = pio.subTerm();
        return term.op() == integerLDT.getAdd()
                && term.sub(0).op() == integerLDT.getNumberSymbol()
                && term.sub(1).op() == integerLDT.getNumberSymbol();
    }

    @Override
    public RewriteTaclet generate(Goal goal, PosInOccurrence pio) {
        final Services services = goal.proof().getServices();
        final JTerm find = (JTerm) pio.subTerm();

        final BigInteger left =
            new BigInteger(AbstractTermTransformer.convertToDecimalString(find.sub(0), services));
        final BigInteger right =
            new BigInteger(AbstractTermTransformer.convertToDecimalString(find.sub(1), services));
        final JTerm sum = services.getTermBuilder().zTerm(left.add(right).toString());

        final RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        // the name is derived from the term content only, so that replay and reuse across
        // branches resolve to the same taclet
        tb.setName(MiscTools.toValidTacletName(NAME + "_" + left + "_" + right));
        tb.setDisplayName(NAME.toString());
        tb.setFind(find);
        tb.addGoalTerm(sum);
        tb.addRuleSet(new RuleSet(new Name("concrete")));
        return tb.getTaclet();
    }
}
