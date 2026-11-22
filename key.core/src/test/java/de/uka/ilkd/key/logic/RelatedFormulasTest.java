/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for {@link RelatedFormulas}, in particular the computation of the formulae that are
 * transitively related to a term by shared syntactic subterms.
 */
class RelatedFormulasTest {

    private final Sort sort = new SortImpl(new Name("S1"));
    private final LogicVariable x = new LogicVariable(new Name("x"), sort);
    private final LogicVariable y = new LogicVariable(new Name("y"), sort);
    private final LogicVariable z = new LogicVariable(new Name("z"), sort);
    private final LogicVariable u = new LogicVariable(new Name("u"), sort);
    private final LogicVariable a = new LogicVariable(new Name("a"), sort);

    private JTerm var(LogicVariable v) {
        return new TermImpl(v, ImmutableList.of(), ImmutableList.of());
    }

    private JFunction pred(String name, Sort... argSorts) {
        return new JFunction(new Name(name), JavaDLTheory.FORMULA, argSorts);
    }

    private JTerm atom(JFunction f, JTerm... args) {
        return new TermImpl(f, ImmutableList.of(args), ImmutableList.of());
    }

    @Test
    void directAndSharingFormulasAreKept() {
        SequentFormula f1 = new SequentFormula(atom(pred("p", sort, sort), var(x), var(y)));
        SequentFormula f2 = new SequentFormula(atom(pred("q", sort), var(x)));
        SequentFormula unrelated = new SequentFormula(atom(pred("r", sort), var(u)));
        Sequent seq =
            JavaDLSequentKit.createSequent(ImmutableList.of(f1, f2, unrelated), ImmutableList.of());

        Optional<Set<SequentFormula>> kept = RelatedFormulas.computeKeptFormulas(seq, var(x), f1);

        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactlyInAnyOrder(f1, f2);
    }

    @Test
    void chainIsTransitive() {
        SequentFormula fP = new SequentFormula(atom(pred("p", sort, sort), var(x), var(y)));
        SequentFormula fQ = new SequentFormula(atom(pred("q", sort, sort), var(y), var(z)));
        SequentFormula fR = new SequentFormula(atom(pred("r", sort), var(z)));
        SequentFormula fS = new SequentFormula(atom(pred("s", sort), var(u)));
        Sequent seq =
            JavaDLSequentKit.createSequent(ImmutableList.of(fP, fQ, fR, fS), ImmutableList.of());

        Optional<Set<SequentFormula>> kept = RelatedFormulas.computeKeptFormulas(seq, var(x), fP);

        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactlyInAnyOrder(fP, fQ, fR);
    }

    @Test
    void seedInsideClickedFormulaOnly() {
        SequentFormula fP = new SequentFormula(atom(pred("P", sort), var(x)));
        SequentFormula fQ = new SequentFormula(atom(pred("Q", sort), var(a)));
        Sequent seq = JavaDLSequentKit.createSequent(ImmutableList.of(fP, fQ), ImmutableList.of());

        Optional<Set<SequentFormula>> kept = RelatedFormulas.computeKeptFormulas(seq, var(x), fP);

        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactly(fP);
        assertThat(RelatedFormulas.hidesNothing(seq, kept.orElseThrow())).isFalse();
    }

    @Test
    void clickedFormulaAbsentYieldsEmpty() {
        SequentFormula fP = new SequentFormula(atom(pred("P", sort), var(x)));
        SequentFormula absent = new SequentFormula(atom(pred("Q", sort), var(a)));
        Sequent seq = JavaDLSequentKit.createSequent(ImmutableList.of(fP), ImmutableList.of());

        Optional<Set<SequentFormula>> kept =
            RelatedFormulas.computeKeptFormulas(seq, var(x), absent);

        assertThat(kept).isEmpty();
    }

    @Test
    void allRelatedIsNothingToHide() {
        SequentFormula fP = new SequentFormula(atom(pred("P", sort), var(x)));
        Sequent seq = JavaDLSequentKit.createSequent(ImmutableList.of(fP), ImmutableList.of());

        Optional<Set<SequentFormula>> kept = RelatedFormulas.computeKeptFormulas(seq, var(x), fP);

        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactly(fP);
        assertThat(RelatedFormulas.hidesNothing(seq, kept.orElseThrow())).isTrue();
    }

    @Test
    void duplicateSharedSubtermConnects() {
        JTerm tx = var(x);
        SequentFormula f1 = new SequentFormula(atom(pred("p", sort, sort), tx, var(y)));
        SequentFormula f2 = new SequentFormula(atom(pred("p", sort, sort), tx, var(z)));
        SequentFormula fR = new SequentFormula(atom(pred("r", sort), var(u)));
        Sequent seq =
            JavaDLSequentKit.createSequent(ImmutableList.of(f1, f2, fR), ImmutableList.of());

        Optional<Set<SequentFormula>> kept = RelatedFormulas.computeKeptFormulas(seq, tx, f1);

        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactlyInAnyOrder(f1, f2);
    }

    @Test
    void alphaVariantBoundVarNotConnected() {
        LogicVariable boundX = new LogicVariable(new Name("x"), sort);
        LogicVariable boundY = new LogicVariable(new Name("y"), sort);
        // forall x. P(x) and forall y. P(y) with distinct bound variables are
        // structurally different terms: they must NOT be connected.
        SequentFormula f1 = new SequentFormula(
            new TermImpl(de.uka.ilkd.key.logic.op.Quantifier.ALL,
                ImmutableList.of(atom(pred("P", sort), var(boundX))),
                ImmutableList.of(boundX)));
        SequentFormula f2 = new SequentFormula(
            new TermImpl(de.uka.ilkd.key.logic.op.Quantifier.ALL,
                ImmutableList.of(atom(pred("P", sort), var(boundY))),
                ImmutableList.of(boundY)));
        Sequent seq = JavaDLSequentKit.createSequent(ImmutableList.of(f1, f2), ImmutableList.of());

        Optional<Set<SequentFormula>> kept =
            RelatedFormulas.computeKeptFormulas(seq, var(boundX), f1);

        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactly(f1);
    }
}
