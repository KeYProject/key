/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.*;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;

/**
 * A JML specification case (i.e., more or less an operation contract) in textual form. Is also used
 * for block contracts.
 */
public final class TextualJMLSpecCase extends TextualJMLConstruct {

    public @NonNull ImmutableList<LabeledParserRuleContext> getRequiresFree(@NonNull Name toString) {
        return getList(REQUIRES_FREE, toString);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getEnsuresFree(@NonNull Name toString) {
        return getList(ENSURES_FREE, toString);
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    public @NonNull ImmutableList<LabeledParserRuleContext> getAssignableFree(@NonNull Name toString) {
        return getList(ASSIGNABLE_FREE, toString);
    }

    private @NonNull ImmutableList<LabeledParserRuleContext> getList(@NonNull ClauseHd clause,
                                                                     @NonNull Name heap) {
        List<LabeledParserRuleContext> seq =
            clauses.stream().filter(it -> it.clauseType.equals(clause))
                    .filter(it -> Objects.equals(it.heap, heap)).map(it -> it.ctx)
                    .collect(Collectors.toList());
        return ImmutableList.fromList(seq);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getAccessible(@NonNull Name heap) {
        return getList(ACCESSIBLE, heap);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getAxioms(@NonNull Name heap) {
        return getList(AXIOMS, heap);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getEnsures(@NonNull Name heap) {
        return getList(ENSURES, heap);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getRequires(@NonNull Name heap) {
        return getList(REQUIRES, heap);
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    public @NonNull ImmutableList<LabeledParserRuleContext> getAssignable(@NonNull Name heap) {
        return getList(ASSIGNABLE, heap);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getDecreases() {
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
     * Note that the name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    public enum ClauseHd {
        ACCESSIBLE, ASSIGNABLE, ASSIGNABLE_FREE, REQUIRES, REQUIRES_FREE, ENSURES, ENSURES_FREE,
        AXIOMS,
    }

    private final @NonNull Behavior behavior;
    private @NonNull ArrayList<Entry> clauses = new ArrayList<>(16);

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

    public TextualJMLSpecCase(ImmutableList<JMLModifier> modifiers, @NonNull Behavior behavior) {
        super(modifiers);
        if (behavior == null) {
            throw new IllegalArgumentException();
        }
        this.behavior = behavior;
    }

    public @NonNull TextualJMLSpecCase addClause(Clause clause, @NonNull LabeledParserRuleContext ctx) {
        if (clauses.isEmpty()) {
            setPosition(ctx);
        }
        clauses.add(new Entry(clause, ctx));
        return this;
    }

    public @NonNull TextualJMLSpecCase addClause(ClauseHd clause, LabeledParserRuleContext ctx) {
        return addClause(clause, null, ctx);
    }

    public @NonNull TextualJMLSpecCase addClause(ClauseHd clause, @Nullable Name heapName,
                                                 LabeledParserRuleContext ctx) {
        if (heapName == null) {
            heapName = HeapLDT.BASE_HEAP_NAME;
        }
        clauses.add(new Entry(clause, ctx, heapName));
        return this;
    }


    public @NonNull TextualJMLSpecCase addClause(Clause clause, ParserRuleContext ctx) {
        return addClause(clause, new LabeledParserRuleContext(ctx));
    }

    public @NonNull TextualJMLSpecCase addClause(ClauseHd clause, ParserRuleContext ctx) {
        return addClause(clause, null, new LabeledParserRuleContext(ctx));
    }

    public @NonNull TextualJMLSpecCase addClause(ClauseHd clause, @Nullable Name heapName,
                                                 ParserRuleContext ctx) {
        return addClause(clause, heapName, new LabeledParserRuleContext(ctx));
    }

    /**
     * Merge clauses of two spec cases. Keep behavior of this one.
     *
     * @param other
     */
    public @NonNull TextualJMLSpecCase merge(@NonNull TextualJMLSpecCase other) {
        TextualJMLSpecCase res = clone();
        res.clauses.addAll(other.clauses);
        return res;
    }

    @Override
    public @NonNull TextualJMLSpecCase clone() {
        TextualJMLSpecCase res = new TextualJMLSpecCase(getModifiers(), getBehavior());
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
    public @NonNull String toString() {
        return "TextualJMLSpecCase{" + "behavior=" + behavior + ", clauses=" + clauses
            + ", modifiers=" + modifiers + ", name='" + name + '\'' + '}';
    }


    // region legacy api
    public void addRequires(LabeledParserRuleContext label) {
        addClause(REQUIRES, label);
    }

    /**
     * An abbreviation is a short-name for a term. Currently unused during the JML translation.
     * A relict from older days ({@link #getAbbreviations()}.
     *
     * @param typeName name of the type
     * @param abbrevName the short-representation of the term
     * @param abbreviatedTerm the term to be abbreviated.
     */
    public record Abbreviation(LabeledParserRuleContext typeName,
            LabeledParserRuleContext abbrevName,
            LabeledParserRuleContext abbreviatedTerm) {
    }

    public Abbreviation @NonNull [] getAbbreviations() {
        /* weigl: prepare for future use of generated abbreviations from JML specifications */
        return new Abbreviation[0];
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getInfFlowSpecs() {
        return getList(INFORMATION_FLOW);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getReturns() {
        return getList(RETURNS);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getContinues() {
        return getList(CONTINUES);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getBreaks() {
        return getList(BREAKS);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getDiverges() {
        return getList(DIVERGES);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getMeasuredBy() {
        return getList(MEASURED_BY);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getSignalsOnly() {
        return getList(SIGNALS_ONLY);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getRequires() {
        return getList(REQUIRES);
    }

    private @NonNull ImmutableList<LabeledParserRuleContext> getList(Object key) {
        List<LabeledParserRuleContext> seq =
            clauses.stream().filter(it -> it.clauseType.equals(key)).map(it -> it.ctx)
                    .collect(Collectors.toList());
        return ImmutableList.fromList(seq);
    }

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    public @NonNull ImmutableList<LabeledParserRuleContext> getAssignable() {
        return getList(ASSIGNABLE);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getEnsures() {
        return getList(ENSURES);
    }

    public @NonNull ImmutableList<LabeledParserRuleContext> getSignals() {
        return getList(SIGNALS);
    }
    // endregion

    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof TextualJMLSpecCase that)) {
            return false;
        }
        return getBehavior() == that.getBehavior() && clauses.equals(that.clauses);
    }

    @Override
    public int hashCode() {
        return Objects.hash(getBehavior(), clauses);
    }
}
