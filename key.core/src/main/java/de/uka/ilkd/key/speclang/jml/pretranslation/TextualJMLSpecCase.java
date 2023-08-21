/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.*;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;

/**
 * A JML specification case (i.e., more or less an operation contract) in textual form. Is also used
 * for block contracts.
 */
public final class TextualJMLSpecCase extends TextualJMLConstruct {

    public ImmutableList<LabeledParserRuleContext> getRequiresFree(Name toString) {
        return getList(REQUIRES_FREE, toString);
    }

    public ImmutableList<LabeledParserRuleContext> getEnsuresFree(Name toString) {
        return getList(ENSURES_FREE, toString);
    }

    public ImmutableList<LabeledParserRuleContext> getAssignableFree(Name toString) {
        return getList(ASSIGNABLE_FREE, toString);
    }

    private ImmutableList<LabeledParserRuleContext> getList(@Nonnull ClauseHd clause,
            @Nonnull Name heap) {
        List<LabeledParserRuleContext> seq =
            clauses.stream().filter(it -> it.clauseType.equals(clause))
                    .filter(it -> Objects.equals(it.heap, heap)).map(it -> it.ctx)
                    .collect(Collectors.toList());
        return ImmutableList.fromList(seq);
    }

    public ImmutableList<LabeledParserRuleContext> getAccessible(Name heap) {
        return getList(ACCESSIBLE, heap);
    }

    public ImmutableList<LabeledParserRuleContext> getAxioms(Name heap) {
        return getList(AXIOMS, heap);
    }

    public ImmutableList<LabeledParserRuleContext> getEnsures(Name heap) {
        return getList(ENSURES, heap);
    }

    public ImmutableList<LabeledParserRuleContext> getRequires(Name heap) {
        return getList(REQUIRES, heap);
    }

    public ImmutableList<LabeledParserRuleContext> getAssignable(Name heap) {
        return getList(ASSIGNABLE, heap);
    }

    public ImmutableList<LabeledParserRuleContext> getDecreases() {
        return getList(DECREASES);
    }

    /**
     * Heap-independent clauses
     */
    public enum Clause {
        MEASURED_BY, WORKING_SPACE, SIGNALS, DIVERGES, DEPENDS, BREAKS, CONTINUES, RETURNS,
        DECREASES, SIGNALS_ONLY, ABBREVIATION, INFORMATION_FLOW
    }

    /**
     * Heap-dependent clauses
     */
    public enum ClauseHd {
        ACCESSIBLE, ASSIGNABLE, ASSIGNABLE_FREE, REQUIRES, REQUIRES_FREE, ENSURES, ENSURES_FREE,
        AXIOMS,
    }

    private final Behavior behavior;
    private ArrayList<Entry> clauses = new ArrayList<>(16);

    static class Entry {
        final Object clauseType;
        final LabeledParserRuleContext ctx;
        final Name heap;

        Entry(Object clauseType, LabeledParserRuleContext ctx, Name heap) {
            this.clauseType = clauseType;
            this.ctx = ctx;
            this.heap = heap;
        }

        Entry(Object clauseType, LabeledParserRuleContext ctx) {
            this(clauseType, ctx, null);
        }
    }

    public TextualJMLSpecCase(ImmutableList<JMLModifier> mods, @Nonnull Behavior behavior) {
        super(mods);
        this.behavior = Objects.requireNonNull(behavior);
    }

    public TextualJMLSpecCase addClause(Clause clause, LabeledParserRuleContext ctx) {
        if (clauses.isEmpty()) {
            setPosition(ctx);
        }
        clauses.add(new Entry(clause, ctx));
        return this;
    }

    public TextualJMLSpecCase addClause(ClauseHd clause, LabeledParserRuleContext ctx) {
        return addClause(clause, null, ctx);
    }

    public TextualJMLSpecCase addClause(ClauseHd clause, @Nullable Name heapName,
            LabeledParserRuleContext ctx) {
        if (heapName == null) {
            heapName = HeapLDT.BASE_HEAP_NAME;
        }
        clauses.add(new Entry(clause, ctx, heapName));
        return this;
    }


    public TextualJMLSpecCase addClause(Clause clause, ParserRuleContext ctx) {
        return addClause(clause, new LabeledParserRuleContext(ctx));
    }

    public TextualJMLSpecCase addClause(ClauseHd clause, ParserRuleContext ctx) {
        return addClause(clause, null, new LabeledParserRuleContext(ctx));
    }

    public TextualJMLSpecCase addClause(ClauseHd clause, @Nullable Name heapName,
            ParserRuleContext ctx) {
        return addClause(clause, heapName, new LabeledParserRuleContext(ctx));
    }

    /**
     * Merge clauses of two spec cases. Keep behavior of this one.
     *
     * @param other
     */
    public @Nonnull TextualJMLSpecCase merge(@Nonnull TextualJMLSpecCase other) {
        TextualJMLSpecCase res = clone();
        res.clauses.addAll(other.clauses);
        return res;
    }

    @Override
    public @Nonnull TextualJMLSpecCase clone() {
        TextualJMLSpecCase res = new TextualJMLSpecCase(getMods(), getBehavior());
        res.name = name;
        res.clauses = new ArrayList<>(clauses);
        return res;
    }

    public void addName(String n) {
        this.name = n;
        // setPosition(n);
    }

    public Behavior getBehavior() {
        return behavior;
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return "TextualJMLSpecCase{" + "behavior=" + behavior + ", clauses=" + clauses + ", mods="
            + mods + ", name='" + name + '\'' + '}';
    }

    // region legacy api
    public void addRequires(LabeledParserRuleContext label) {
        addClause(REQUIRES, label);
    }

    public Triple<LabeledParserRuleContext, LabeledParserRuleContext, LabeledParserRuleContext>[] getAbbreviations() {
        /* weigl: prepare for future use of generated abbreviations from JML specifications */
        return new Triple[0];
    }

    public ImmutableList<LabeledParserRuleContext> getInfFlowSpecs() {
        return getList(INFORMATION_FLOW);
    }

    public ImmutableList<LabeledParserRuleContext> getReturns() {
        return getList(RETURNS);
    }

    public ImmutableList<LabeledParserRuleContext> getContinues() {
        return getList(CONTINUES);
    }

    public ImmutableList<LabeledParserRuleContext> getBreaks() {
        return getList(BREAKS);
    }

    public ImmutableList<LabeledParserRuleContext> getDiverges() {
        return getList(DIVERGES);
    }

    public ImmutableList<LabeledParserRuleContext> getMeasuredBy() {
        return getList(MEASURED_BY);
    }

    public ImmutableList<LabeledParserRuleContext> getSignalsOnly() {
        return getList(SIGNALS_ONLY);
    }

    public ImmutableList<LabeledParserRuleContext> getRequires() {
        return getList(REQUIRES);
    }

    private ImmutableList<LabeledParserRuleContext> getList(Object key) {
        List<LabeledParserRuleContext> seq =
            clauses.stream().filter(it -> it.clauseType.equals(key)).map(it -> it.ctx)
                    .collect(Collectors.toList());
        return ImmutableList.fromList(seq);
    }

    public ImmutableList<LabeledParserRuleContext> getAssignable() {
        return getList(ASSIGNABLE);
    }

    public ImmutableList<LabeledParserRuleContext> getEnsures() {
        return getList(ENSURES);
    }

    public ImmutableList<LabeledParserRuleContext> getSignals() {
        return getList(SIGNALS);
    }
    // endregion

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof TextualJMLSpecCase)) {
            return false;
        }
        TextualJMLSpecCase that = (TextualJMLSpecCase) o;
        return getBehavior() == that.getBehavior() && clauses.equals(that.clauses);
    }

    @Override
    public int hashCode() {
        return Objects.hash(getBehavior(), clauses);
    }
}
