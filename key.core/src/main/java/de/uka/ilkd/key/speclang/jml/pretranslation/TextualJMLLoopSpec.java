/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.*;
import java.util.stream.Collectors;
import javax.annotation.Nullable;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * A JML loop specification (invariant, assignable clause, decreases clause, ...) in textual form.
 */
public final class TextualJMLLoopSpec extends TextualJMLConstruct {
    private LabeledParserRuleContext variant = null;
    private final ArrayList<Entry> clauses = new ArrayList<>(16);

    /**
     * Heap-dependent clauses
     */
    public enum ClauseHd {
        INFORMATION_FLOW, ASSIGNABLE, ASSIGNABLE_FREE, INVARIANT, INVARIANT_FREE
    }

    public TextualJMLLoopSpec(ImmutableList<JMLModifier> mods) {
        super(mods);
    }

    /*
     * public TextualJMLLoopSpec addClause(Clause clause, LabeledParserRuleContext ctx) {
     * clauses.add(new Entry(clause, ctx)); return this; }
     */

    public TextualJMLLoopSpec addClause(ClauseHd clause, LabeledParserRuleContext ctx) {
        return addClause(clause, null, ctx);
    }

    public TextualJMLLoopSpec addClause(ClauseHd clause, @Nullable Name heapName,
            LabeledParserRuleContext ctx) {
        if (heapName == null) {
            heapName = HeapLDT.BASE_HEAP_NAME;
        }
        if (clauses.isEmpty()) {
            setPosition(ctx);
        }
        clauses.add(new Entry(clause, ctx, heapName));
        return this;
    }

    public void setVariant(LabeledParserRuleContext ps) {
        assert variant == null;
        variant = ps;
        setPosition(ps);
    }

    private ImmutableList<LabeledParserRuleContext> getList(Object key) {
        final List<LabeledParserRuleContext> seq =
            clauses.stream().filter(it -> it.clauseType.equals(key)).map(it -> it.ctx)
                    .collect(Collectors.toList());
        return ImmutableList.fromList(seq);
    }

    public ImmutableList<LabeledParserRuleContext> getAssignable() {
        return getList(ClauseHd.ASSIGNABLE);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getAssignables() {
        return getMap(ClauseHd.ASSIGNABLE);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getAssignablesInit() {
        return getMapInit(ClauseHd.ASSIGNABLE);
    }

    public ImmutableList<LabeledParserRuleContext> getAssignableFree() {
        return getList(ClauseHd.ASSIGNABLE_FREE);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getAssignablesFree() {
        return getMap(ClauseHd.ASSIGNABLE_FREE);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getAssignablesFreeInit() {
        return getMapInit(ClauseHd.ASSIGNABLE_FREE);
    }

    public ImmutableList<LabeledParserRuleContext> getInfFlowSpecs() {
        return getList(ClauseHd.INFORMATION_FLOW);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getInvariants() {
        return getMap(ClauseHd.INVARIANT);
    }

    private Map<String, ImmutableList<LabeledParserRuleContext>> getMapInit(ClauseHd clause) {
        Name defaultHeap = HeapLDT.BASE_HEAP_NAME;
        Map<String, ImmutableList<LabeledParserRuleContext>> map = new HashMap<>();
        for (Entry entry : clauses) {
            if (clause.equals(entry.clauseType)) {
                String h = (entry.heap != null ? entry.heap : defaultHeap).toString();
                ImmutableList<LabeledParserRuleContext> l =
                    map.getOrDefault(h, ImmutableSLList.nil());
                map.put(h, l.append(entry.ctx));
            }
        }

        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            if (!map.containsKey(h.toString())) {
                map.put(h.toString(), ImmutableSLList.nil());
            }
        }
        return map;
    }

    private Map<String, ImmutableList<LabeledParserRuleContext>> getMap(ClauseHd clause) {
        Name defaultHeap = HeapLDT.BASE_HEAP_NAME;
        Map<String, ImmutableList<LabeledParserRuleContext>> map = new HashMap<>();
        for (Entry entry : clauses) {
            if (clause.equals(entry.clauseType)) {
                String h = (entry.heap != null ? entry.heap : defaultHeap).toString();
                ImmutableList<LabeledParserRuleContext> l =
                    map.getOrDefault(h, ImmutableSLList.nil());
                map.put(h, l.append(entry.ctx));
            }
        }

        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            if (!map.containsKey(h.toString())) {
                map.put(h.toString(), ImmutableSLList.nil());
            }
        }
        return map;
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getFreeInvariants() {
        return getMap(ClauseHd.INVARIANT_FREE);
    }

    public LabeledParserRuleContext getVariant() {
        return variant;
    }

    /*
     * @Override public String toString() { StringBuffer sb = new StringBuffer();
     * Iterator<LabeledParserRuleContext> it;
     *
     * for (Name heap : HeapLDT.VALID_HEAP_NAMES) { it = invariants.get(heap.toString()).iterator();
     * while (it.hasNext()) { sb.append("invariant<" + heap + ">: " + it.next() + "\n"); } } for
     * (Name heap : HeapLDT.VALID_HEAP_NAMES) { it = freeInvariants.get(heap.toString()).iterator();
     * while (it.hasNext()) { sb.append("free invariant<" + heap + ">: " + it.next() + "\n"); } }
     * for (Name heap : HeapLDT.VALID_HEAP_NAMES) { it =
     * assignables.get(heap.toString()).iterator(); while (it.hasNext()) { sb.append("assignable<" +
     * heap + ">: " + it.next() + "\n"); } } for (Name heap : HeapLDT.VALID_HEAP_NAMES) { it =
     * infFlowSpecs.iterator(); while (it.hasNext()) { sb.append("determines<" + heap + ">: " +
     * it.next() + "\n"); } } if (variant != null) { sb.append("decreases: " + variant); }
     *
     * return sb.toString(); }
     */


    @Override
    public String toString() {
        return "TextualJMLLoopSpec{" + "variant=" + variant + ", clauses=" + clauses + '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        TextualJMLLoopSpec that = (TextualJMLLoopSpec) o;
        return variant.equals(that.variant) && clauses.equals(that.clauses);
    }

    @Override
    public int hashCode() {
        return Objects.hash(variant, clauses);
    }

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
}
