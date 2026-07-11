/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.ccatch.CcatchReturnValParameterDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.FieldReference;
import de.uka.ilkd.key.java.ast.reference.SchemaTypeReference;
import de.uka.ilkd.key.java.ast.reference.SchematicFieldReference;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.reference.TypeReferenceImp;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.TransactionStatement;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchContextStatementBlockInstruction;
import de.uka.ilkd.key.rule.match.vm.instructions.MatchSchemaTypeReferenceInstruction;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.compiler.ProgramChildCursor;
import org.key_project.prover.rules.matcher.compiler.ProgramChildSequence;
import org.key_project.prover.rules.matcher.compiler.ProgramLeafPlan;
import org.key_project.prover.rules.matcher.compiler.ProgramListSVPlan;
import org.key_project.prover.rules.matcher.compiler.ProgramMatchPlan;
import org.key_project.prover.rules.matcher.compiler.ProgramStructuralPlan;
import org.key_project.prover.rules.matcher.vm.MatchProgram;
import org.key_project.prover.rules.matcher.vm.VMProgramInterpreter;
import org.key_project.prover.rules.matcher.vm.instruction.MatchByEqualsInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchIdentityInstruction;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.getMatchInstructionForSV;
import static de.uka.ilkd.key.rule.match.vm.instructions.JavaDLMatchVMInstructionSet.gotoNextInstruction;

/**
 * Builds the {@link ProgramMatchPlan} for one Java program (sub)element of a modality. A taclet's
 * find pattern may contain a piece of Java code inside a modality ({@code \<{ ... }\>}); matching
 * decides whether that pattern fits the program of a concrete formula, and binds the pattern's
 * <em>schema variables</em> — placeholders such as {@code #se} or {@code #slist} — to the concrete
 * program parts they stand for (their <em>instantiations</em>).
 *
 * <p>
 * A plan is a single description of how one pattern element is matched, from which both matcher
 * back-ends are derived —
 * {@link ProgramMatchPlan#emit} produces the interpreter's VM instructions and
 * {@link ProgramMatchPlan#compile} the compiled, cursor-free matcher. It is the program-AST
 * counterpart of {@link JavaMatchPlanBuilder} (which does the same for the first-order term
 * skeleton). On the compiled back-end this dispatch is the <em>whole</em> program matcher: it
 * reads only the structure of pattern and source and never calls an AST
 * {@code match(SourceData, MatchConditions)} method. (The interpreter back-end still has its
 * hand-written conversion, {@code SyntaxElementMatchProgramGenerator}, with the monolithic
 * {@code MatchProgramInstruction} beneath it, until it is retired.)
 *
 * <p>
 * The plans form a small immutable tree that mirrors the pattern, with one node kind per way of
 * matching:
 * <ul>
 * <li>{@link LeafPlan} — a plan-tree leaf matched by a single instruction (schema variables,
 * schema type references, and value-carrying leaves such as literals);</li>
 * <li>{@link ListSVPlan} — a list program schema variable, which matches a run of source children
 * and is driven by its enclosing {@link StructuralPlan};</li>
 * <li>{@link StructuralPlan} — the default <b>generic match</b>: same concrete class as the
 * pattern, an optional extra field check (the {@code guard}, e.g. array dimensions), and the
 * children matched recursively;</li>
 * <li>{@link FieldReferencePlan} — a schematic field reference, which accepts any source
 * {@link FieldReference} instead of one exact class;</li>
 * <li>{@link ContextBlockPlan} — the {@code .. ...} context pattern of symbolic-execution
 * taclets.</li>
 * </ul>
 * "Generic" is used throughout in the sense of {@link #isGenericMatch} — the
 * class-identity-plus-children match that {@code JavaProgramElement} /
 * {@code JavaNonTerminalProgramElement} provide by default, for elements that do not override
 * {@code match}. It has nothing to do with Java generics or generic sorts. Each node's
 * {@code toString} renders its subtree, so a whole plan can be printed for debugging.
 *
 * <p>
 * {@link #buildProgramPlan} returns {@code null} for an element this dispatch does not describe.
 * On the compiled back-end the modality then has no head and the taclet fails to load with the
 * framework's clear "no head for this find pattern" error — the same contract the term side has;
 * on the interpreter back-end the conversion falls back to the monolithic matcher. Every construct
 * expressible in the taclet language is described.
 */
public final class JavaProgramMatchPlanBuilder {

    private JavaProgramMatchPlanBuilder() {}

    /**
     * Dispatches on the kind of program element and returns the plan that matches it.
     *
     * @param pe a program (sub)element pattern
     * @return a plan matching {@code pe}, or {@code null} if this dispatch does not describe
     *         {@code pe}'s kind (see the class comment for what the two back-ends do then)
     */
    public static @Nullable ProgramMatchPlan buildProgramPlan(SyntaxElement pe) {
        // The dispatch order is significant: a subtype must be checked before its supertype
        // (SchemaTypeReference extends TypeReferenceImp), and ProgramElementName is a Name, not a
        // ProgramElement, so it must be handled before the ProgramElement gate below.
        if (pe instanceof ProgramSV psv) {
            return psv.isListSV() ? new ProgramListSVPlan(psv)
                    : new ProgramLeafPlan(psv, getMatchInstructionForSV(psv));
        }
        if (pe instanceof SchemaTypeReference schemaTypeRef) {
            // matches any concrete type reference with the same simple name and array dimensions
            return new ProgramLeafPlan(schemaTypeRef,
                new MatchSchemaTypeReferenceInstruction(schemaTypeRef));
        }
        if (pe instanceof SchemaVariable) {
            return null; // other schema variables in programs are not describable
        }
        // value-carrying leaves matched by equals (class + payload): Literal (+ subclasses),
        // TransactionStatement, and ProgramElementName (a name identity). They recurse into no
        // children and bind no schema variables.
        if (pe instanceof Literal || pe instanceof TransactionStatement
                || pe instanceof ProgramElementName) {
            return new ProgramLeafPlan(pe, new MatchByEqualsInstruction(pe));
        }
        // concrete program variables and methods occurring literally in a pattern (e.g.
        // "int x = 0;" in a hand-written taclet) match by reference identity, mirroring
        // ProgramVariable.match / ProgramMethod.match
        if (pe instanceof ProgramVariable || pe instanceof ProgramMethod) {
            return new ProgramLeafPlan(pe, getMatchIdentityInstruction(pe));
        }
        if (!(pe instanceof ProgramElement progEl)) {
            return null;
        }
        if (progEl instanceof ContextStatementBlock csb) {
            return ContextBlockPlan.of(csb);
        }
        // CcatchReturnValParameterDeclaration overrides match only to delegate to the generic
        // non-terminal super.match, so it is matched generically (exact class + child recursion).
        if (progEl instanceof CcatchReturnValParameterDeclaration) {
            return structuralPlan(progEl, null);
        }
        if (progEl instanceof TypeReferenceImp typeRef) {
            return typeReferencePlan(typeRef);
        }
        if (progEl instanceof VariableSpecification varSpec) {
            return variableSpecificationPlan(varSpec);
        }
        if (progEl instanceof SchematicFieldReference fieldRef) {
            return FieldReferencePlan.of(fieldRef);
        }
        if (!isGenericMatch(progEl)) {
            return null; // overrides match() with logic not described here
        }
        return structuralPlan(progEl, null);
    }

    /**
     * Caches, per program-element class, whether it uses the generic {@code match} (no override).
     */
    private static final Map<Class<?>, Boolean> GENERIC_MATCH = new ConcurrentHashMap<>();

    /**
     * @return whether the element's class uses the generic
     *         {@code match(SourceData, MatchConditions)} (declared in {@code JavaProgramElement} or
     *         {@code JavaNonTerminalProgramElement}: class equality + exact-size child recursion)
     *         rather than its own override.
     */
    static boolean isGenericMatch(ProgramElement pe) {
        return GENERIC_MATCH.computeIfAbsent(pe.getClass(), c -> {
            try {
                final Class<?> declaring =
                    c.getMethod("match", SourceData.class, MatchConditions.class)
                            .getDeclaringClass();
                return declaring == JavaProgramElement.class
                        || declaring == JavaNonTerminalProgramElement.class;
            } catch (NoSuchMethodException e) {
                return false;
            }
        });
    }

    /**
     * A concrete type reference {@code TypeReferenceImp}: a generic match that additionally
     * requires the source to be a {@link TypeReference} with the same number of array
     * {@code dimensions}.
     */
    private static @Nullable ProgramMatchPlan typeReferencePlan(TypeReferenceImp pattern) {
        final int dimensions = pattern.getDimensions();
        final MatchInstruction guard = (actual, mc, services) -> actual instanceof TypeReference tr
                && tr.getDimensions() == dimensions ? mc : null;
        return structuralPlan(pattern, guard);
    }

    /**
     * A {@code VariableSpecification}: a generic match that additionally requires the source
     * specification to have the same number of array {@code dimensions}.
     */
    private static @Nullable ProgramMatchPlan variableSpecificationPlan(
            VariableSpecification pattern) {
        final int dimensions = pattern.getDimensions();
        final MatchInstruction guard =
            (actual, mc, services) -> actual instanceof VariableSpecification vs
                    && vs.getDimensions() == dimensions ? mc : null;
        return structuralPlan(pattern, guard);
    }

    /**
     * Builds the plans for {@code pe}'s children and combines them into a structural plan (same
     * concrete class, optional {@code guard}, children matched recursively). Returns {@code null}
     * if some child cannot be described by the dispatch.
     */
    private static @Nullable ProgramMatchPlan structuralPlan(ProgramElement pe,
            @Nullable MatchInstruction guard) {
        final int childCount = pe.getChildCount();
        final ProgramMatchPlan[] children = new ProgramMatchPlan[childCount];
        for (int i = 0; i < childCount; i++) {
            final ProgramMatchPlan child = buildProgramPlan(pe.getChild(i));
            if (child == null) {
                return null;
            }
            children[i] = child;
        }
        return new ProgramStructuralPlan(pe, guard, children, JavaListSVMatcher.INSTANCE);
    }



    /**
     * A {@code SchematicFieldReference} ({@code #ref.#field}). Unlike a generic match it accepts
     * <em>any</em> source that is a {@link FieldReference} (an {@code instanceof} check, not exact
     * class), then matches its children — the reference prefix and the field program schema
     * variable — one-to-one against the source's children, requiring the same child count. As in
     * {@link LeafPlan}, the head check is one instruction object shared by both back-ends.
     */
    private static final class FieldReferencePlan implements ProgramMatchPlan {
        /** any source {@link FieldReference} with the same child count as the pattern. */
        private final MatchInstruction head;
        private final ProgramMatchPlan[] children;
        private final boolean interpretable;

        private FieldReferencePlan(ProgramMatchPlan[] children, boolean interpretable) {
            final int childCount = children.length;
            this.head = (actual, mc, services) -> actual instanceof FieldReference
                    && actual.getChildCount() == childCount ? mc : null;
            this.children = children;
            this.interpretable = interpretable;
        }

        /**
         * @return the plan matching {@code pattern}, or {@code null} if some child cannot be
         *         described by the dispatch or is a list SV (unexpected in a field reference, so
         *         fall back rather than special-case it)
         */
        static @Nullable FieldReferencePlan of(SchematicFieldReference pattern) {
            final int childCount = pattern.getChildCount();
            final ProgramMatchPlan[] children = new ProgramMatchPlan[childCount];
            boolean interpretable = true;
            for (int i = 0; i < childCount; i++) {
                final ProgramMatchPlan child = buildProgramPlan(pattern.getChild(i));
                if (child == null || child.listSV() != null) {
                    return null;
                }
                children[i] = child;
                interpretable &= child.interpretable();
            }
            return new FieldReferencePlan(children, interpretable);
        }

        @Override
        public boolean interpretable() {
            return interpretable;
        }

        @Override
        public void emit(List<VMInstruction> out) {
            out.add(head);
            out.add(gotoNextInstruction());
            for (final ProgramMatchPlan child : children) {
                child.emit(out);
            }
        }

        @Override
        public MatchProgram compile() {
            final MatchProgram[] compiledChildren = new MatchProgram[children.length];
            for (int i = 0; i < children.length; i++) {
                compiledChildren[i] = children[i].compile();
            }
            return (actual, mc, services) -> {
                final MatchResultInfo r = head.match(actual, mc, services);
                if (r == null) {
                    return null;
                }
                return ProgramChildSequence.matchOneToOne(compiledChildren, actual, r,
                    services);
            };
        }

        @Override
        public String toString() {
            return "fieldRef" + Arrays.toString(children);
        }
    }

    /**
     * A {@link ContextStatementBlock} — the {@code .. ...} pattern with which taclets match a
     * program at its current execution point. Such a pattern matches statements (the <em>active
     * statements</em>, written between {@code ..} and {@code ...}) that sit inside an arbitrary
     * nesting of blocks, try-catch statements, labels and method frames. The leading {@code ..}
     * stands for that surrounding nesting, called the <em>prefix</em>; the trailing {@code ...}
     * stands for whatever follows the active statements, called the <em>suffix</em>.
     *
     * <p>
     * The compiled matcher performs the whole context match by reading the structure of the
     * source, in four steps:
     * <ol>
     * <li><b>locate the active statements</b>: walk down the source's chain of nested prefix
     * elements until the remaining nesting is exactly as deep as the pattern's own. This yields
     * the parent element and the child index at which the source's active statements begin (index
     * {@code -1} means the located element itself is the match target, e.g. an empty
     * block);</li>
     * <li><b>match the execution context</b>: the execution context says in which class, method
     * and on which object the active statements run — needed, for example, to resolve field
     * accesses and method calls during matching. It is taken from the source's innermost method
     * frame (the statement KeY wraps around an inlined method body), or is the default context if
     * there is none. If the pattern names an execution context of its own ({@code .#ex..} or
     * {@code .#pm@#t(#v)..}), it is matched against the found one. The found context is then
     * recorded with the instantiations;</li>
     * <li><b>match the active statements</b>: each active-statement sub-plan consumes exactly one
     * source child (a list schema variable consumes a run of children);</li>
     * <li><b>record the context</b>: store the position where the prefix ends and the position
     * where the suffix starts (as paths into the source program) in the <em>context
     * instantiation</em> — when the taclet is applied, the new program is assembled around these
     * two positions.</li>
     * </ol>
     *
     * <p>
     * The order of the instantiation updates — execution-context match, recording the context,
     * active statements, final completion — must not be changed: it is observable through the
     * iteration order of the instantiation map. The interpreter back-end ({@link #emit}) does not
     * use these steps; it delegates to {@code ContextStatementBlock.match}, which must produce
     * identical results.
     */
    private static final class ContextBlockPlan implements ProgramMatchPlan {
        private final ContextStatementBlock csb;
        /**
         * the pattern's own prefix length (a per-pattern constant, {@code >= 1}: the block itself
         * counts as one prefix element)
         */
        private final int patternPrefixLength;
        /** plan for the pattern's execution context (child 0), or {@code null} if it has none. */
        private final @Nullable ProgramMatchPlan ecPlan;
        private final ProgramMatchPlan[] active;
        private final boolean interpretable;

        private ContextBlockPlan(ContextStatementBlock csb, @Nullable ProgramMatchPlan ecPlan,
                ProgramMatchPlan[] active, boolean interpretable) {
            this.csb = csb;
            this.patternPrefixLength = csb.getPrefixLength();
            this.ecPlan = ecPlan;
            this.active = active;
            this.interpretable = interpretable;
        }

        /**
         * @return the plan matching {@code csb}, or {@code null} if the execution context or an
         *         active statement cannot be described by the dispatch
         */
        static @Nullable ContextBlockPlan of(ContextStatementBlock csb) {
            assert csb.getPrefixLength() > 0;
            ProgramMatchPlan ecPlan = null;
            if (csb.getExecutionContext() != null) {
                // the pattern's execution context: a ProgramSV (.#ex..) or an ExecutionContext
                // element with schema children (.#pm@#t(#v)..) -- both described by the dispatch
                ecPlan = buildProgramPlan((SyntaxElement) csb.getExecutionContext());
                if (ecPlan == null || ecPlan.listSV() != null) {
                    return null;
                }
            }
            final int offset = csb.getExecutionContext() == null ? 0 : 1;
            final int childCount = csb.getChildCount();
            final ProgramMatchPlan[] active = new ProgramMatchPlan[childCount - offset];
            boolean interpretable = true;
            for (int i = offset; i < childCount; i++) {
                final ProgramMatchPlan p = buildProgramPlan(csb.getChildAt(i));
                if (p == null) {
                    return null;
                }
                active[i - offset] = p;
                // an active statement that is itself a list SV makes the block variable-arity;
                // like every list SV it is compiled-only
                interpretable &= p.interpretable();
            }
            return new ContextBlockPlan(csb, ecPlan, active, interpretable);
        }

        @Override
        public boolean interpretable() {
            return interpretable;
        }

        @Override
        public void emit(List<VMInstruction> out) {
            final List<VMInstruction> activeInstr = new ArrayList<>();
            for (final ProgramMatchPlan p : active) {
                p.emit(activeInstr);
            }
            out.add(new MatchContextStatementBlockInstruction(csb,
                new VMProgramInterpreter(activeInstr.toArray(new VMInstruction[0]))));
        }

        @Override
        public MatchProgram compile() {
            final ProgramChildSequence activeSequence =
                ProgramChildSequence.compile(active, JavaListSVMatcher.INSTANCE);
            final MatchProgram ecMatch = ecPlan == null ? null : ecPlan.compile();
            final int prefixLength = patternPrefixLength;
            return (actual, mc, services) -> matchContext((ProgramElement) actual,
                (MatchConditions) mc, (Services) services, prefixLength, ecMatch,
                activeSequence);
        }

        /**
         * Matches the whole context pattern against the source program {@code src}, in the four
         * steps described in the class comment. The pattern enters only through its prefix length,
         * its execution-context matcher and its active-statement matchers.
         */
        private static @Nullable MatchConditions matchContext(ProgramElement src,
                MatchConditions matchCond, Services services, int patternPrefixLength,
                @Nullable MatchProgram ecMatch, ProgramChildSequence activeSequence) {
            if (matchCond.getInstantiations().getContextInstantiation() != null) {
                // several context statement block occurrences in find or assumes clauses are not
                // allowed
                return null;
            }

            ExecutionContext lastExecutionContext = null;
            final ProgramPrefix prefix;
            int pos = -1;
            PosInProgram relPos = PosInProgram.TOP;
            // the element whose children are the source's active statements, and the child index
            // of the first one (-1: the element itself is the match target, e.g. an empty block)
            ProgramElement activeParent = src;
            int start = -1;

            // step 1: locate the active statements under the source's prefix nesting
            if (src instanceof ProgramPrefix) {
                prefix = (ProgramPrefix) src;
                final int srcPrefixLength = prefix.getPrefixLength();
                if (patternPrefixLength > srcPrefixLength) {
                    return null;
                }
                pos = srcPrefixLength - patternPrefixLength;
                ProgramPrefix firstActiveStatement = getPrefixElementAt(prefix, pos);
                relPos = firstActiveStatement.getFirstActiveChildPos();
                if (relPos != PosInProgram.TOP) {
                    if (firstActiveStatement instanceof MethodFrame) {
                        lastExecutionContext =
                            (ExecutionContext) ((MethodFrame) firstActiveStatement)
                                    .getExecutionContext();
                    }
                    start = relPos.get(relPos.depth() - 1);
                    if (relPos.depth() > 1) {
                        firstActiveStatement = (ProgramPrefix) PosInProgram
                                .getProgramAt(relPos.up(), firstActiveStatement);
                    }
                }
                activeParent = firstActiveStatement;
            } else {
                prefix = null;
            }

            // step 2: match and record the execution context
            matchCond = matchInnerExecutionContext(matchCond, services, lastExecutionContext,
                prefix, ecMatch, src);
            if (matchCond == null) {
                return null;
            }

            // step 3: match the active statements
            final ProgramChildCursor newSource = new ProgramChildCursor(activeParent, start);
            matchCond = matchActiveStatements(newSource, matchCond, services, activeSequence);
            if (matchCond == null) {
                return null;
            }

            // step 4: record the prefix-end and suffix-start positions
            return makeContextInfoComplete(matchCond, newSource, prefix, pos, relPos, src,
                services);
        }

        /**
         * Step 2: determines the source's execution context (the one of the prefix's innermost
         * method frame, or the default context if there is none), matches the pattern's execution
         * context against it if the pattern has one, and records the found context with the
         * instantiations. The prefix-end and suffix-start positions are not known yet at this
         * point; they are filled in by {@link #makeContextInfoComplete} after the active
         * statements have been matched.
         */
        private static @Nullable MatchConditions matchInnerExecutionContext(
                MatchConditions matchCond, Services services,
                @Nullable ExecutionContext lastExecutionContext, @Nullable ProgramPrefix prefix,
                @Nullable MatchProgram ecMatch, ProgramElement src) {
            ExecutionContext innerContext = lastExecutionContext;
            if (innerContext == null) {
                if (prefix != null && prefix.getInnerMostMethodFrame() != null) {
                    innerContext = (ExecutionContext) prefix.getInnerMostMethodFrame()
                            .getExecutionContext();
                } else {
                    innerContext = services.getJavaInfo().getDefaultExecutionContext();
                }
            }
            if (ecMatch != null) {
                matchCond = (MatchConditions) ecMatch.match(innerContext, matchCond, services);
                if (matchCond == null) {
                    return null;
                }
            }
            return matchCond.setInstantiations(
                matchCond.getInstantiations().add(null, null, innerContext, src, services));
        }

        /**
         * Step 3: matches the active statements. In the common case — no list schema variable
         * among them, and the match starts at a regular child index — each sub-matcher is applied
         * directly to its source child, and the cursor is then advanced past the matched children.
         * Otherwise a cursor walks the source children one by one: an active statement that is a
         * list schema variable consumes a greedy run of children, and a start index of {@code -1}
         * means the first sub-matcher consumes the located element itself (an empty block or empty
         * try). The pattern need not consume all source children — whatever remains belongs to the
         * context's suffix.
         *
         * <p>
         * When the source runs out of children before the pattern's active statements are
         * exhausted, the match simply fails. (The interpreter back-end instead crashes with a
         * {@code NullPointerException} if the leftover pattern statement is a childless terminal —
         * its AST matcher does not null-check; failing cleanly here is deliberate. No shipped
         * taclet has such a shape.)
         */
        private static @Nullable MatchConditions matchActiveStatements(
                ProgramChildCursor newSource, MatchConditions matchCond, Services services,
                ProgramChildSequence activeSequence) {
            final int n = activeSequence.size();
            final int start = newSource.getChildPos();
            if (!activeSequence.isVarArity() && start >= 0) {
                if (!(newSource.getElement() instanceof NonTerminalProgramElement ntParent)
                        || ntParent.getChildCount() < start + n) {
                    // not enough source children -> matching would fail on a null source child
                    return null;
                }
                matchCond = (MatchConditions) activeSequence.matchOneToOneFrom(ntParent, start,
                    matchCond, services);
                if (matchCond == null) {
                    return null;
                }
                newSource.setChildPos(start + n);
            } else {
                matchCond =
                    (MatchConditions) activeSequence.match(newSource, matchCond, services);
                if (matchCond == null) {
                    return null;
                }
            }
            return matchCond;
        }

        /**
         * Step 4: computes the position where the prefix ends and the position where the suffix
         * starts, and completes the context instantiation with them. The execution context is
         * re-read from the instantiations because step 2 may have bound it there.
         */
        private static MatchConditions makeContextInfoComplete(MatchConditions matchCond,
                ProgramChildCursor newSource, @Nullable ProgramPrefix prefix, int pos,
                PosInProgram relPos, ProgramElement src, Services services) {
            final SVInstantiations instantiations = matchCond.getInstantiations();
            final ExecutionContext lastExecutionContext = instantiations.getExecutionContext();
            final PosInProgram prefixEnd = matchPrefixEnd(prefix, pos, relPos);
            // position of the first source element that is not matched (start of the suffix)
            final int lastMatchedPos = newSource.getChildPos();
            final PosInProgram suffixStart = prefixEnd.up().down(lastMatchedPos);
            return matchCond.setInstantiations(instantiations.replace(prefixEnd, suffixStart,
                lastExecutionContext, src, services));
        }

        /**
         * Computes the position of the first element that is not part of the source's prefix, by
         * concatenating the active-child positions of the first {@code pos + 1} prefix elements.
         */
        private static PosInProgram matchPrefixEnd(@Nullable ProgramPrefix prefix, int pos,
                PosInProgram relPos) {
            PosInProgram prefixEnd = PosInProgram.TOP;
            if (prefix != null) {
                ProgramPrefix currentPrefix = prefix;
                int i = 0;
                while (i <= pos) {
                    prefixEnd = prefixEnd.append(currentPrefix.getFirstActiveChildPos());
                    i++;
                    if (i <= pos) {
                        currentPrefix = currentPrefix.getNextPrefixElement();
                    }
                }
            } else {
                prefixEnd = relPos;
            }
            return prefixEnd;
        }

        /** the {@code i}-th element of the source's prefix chain (element {@code 0} = the start) */
        private static ProgramPrefix getPrefixElementAt(ProgramPrefix prefix, int i) {
            ProgramPrefix current = prefix;
            for (int pos = 0; pos < i; pos++) {
                current = current.getNextPrefixElement();
            }
            return current;
        }

        @Override
        public String toString() {
            return "context" + (ecPlan == null ? "" : "(ec " + ecPlan + ")")
                + Arrays.toString(active);
        }
    }
}
