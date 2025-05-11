/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT_FREE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.*;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;
import static de.uka.ilkd.key.speclang.njml.Translator.raiseError;

class TextualTranslator extends JmlParserBaseVisitor<Object> {
    private final boolean attachOriginLabel;

    public @NonNull ImmutableList<TextualJMLConstruct> constructs = ImmutableSLList.nil();
    private @NonNull ImmutableList<JMLModifier> mods = ImmutableSLList.nil();
    private @Nullable TextualJMLSpecCase methodContract;
    private @Nullable TextualJMLLoopSpec loopContract;

    /**
     * Translates a token to a JMLModifier
     *
     * @param token the token
     * @return the modifier
     */
    public static JMLModifier modifierFromToken(@Nullable Token token) {
        if (token == null) {
            return null;
        }

        return switch (token.getType()) {
        case JmlLexer.ABSTRACT -> JMLModifier.ABSTRACT;
        case JmlLexer.FINAL -> JMLModifier.FINAL;
        case JmlLexer.GHOST -> JMLModifier.GHOST;
        case JmlLexer.HELPER -> JMLModifier.HELPER;
        case JmlLexer.INSTANCE -> JMLModifier.INSTANCE;
        case JmlLexer.MODEL -> JMLModifier.MODEL;
        case JmlLexer.NON_NULL -> JMLModifier.NON_NULL;
        case JmlLexer.NULLABLE -> JMLModifier.NULLABLE;
        case JmlLexer.NULLABLE_BY_DEFAULT -> JMLModifier.NULLABLE_BY_DEFAULT;
        case JmlLexer.PRIVATE -> JMLModifier.PRIVATE;
        case JmlLexer.PROTECTED -> JMLModifier.PROTECTED;
        case JmlLexer.PUBLIC -> JMLModifier.PUBLIC;
        case JmlLexer.PURE -> JMLModifier.PURE;
        case JmlLexer.STRICTLY_PURE -> JMLModifier.STRICTLY_PURE;
        case JmlLexer.SPEC_PROTECTED -> JMLModifier.SPEC_PROTECTED;
        case JmlLexer.SPEC_PUBLIC -> JMLModifier.SPEC_PUBLIC;
        case JmlLexer.STATIC -> JMLModifier.STATIC;
        case JmlLexer.TWO_STATE -> JMLModifier.TWO_STATE;
        case JmlLexer.NO_STATE -> JMLModifier.NO_STATE;
        case JmlLexer.SPEC_JAVA_MATH -> JMLModifier.SPEC_JAVA_MATH;
        case JmlLexer.SPEC_SAFE_MATH -> JMLModifier.SPEC_SAFE_MATH;
        case JmlLexer.SPEC_BIGINT_MATH -> JMLModifier.SPEC_BIGINT_MATH;
        case JmlLexer.CODE_JAVA_MATH -> JMLModifier.CODE_JAVA_MATH;
        case JmlLexer.CODE_SAFE_MATH -> JMLModifier.CODE_SAFE_MATH;
        case JmlLexer.CODE_BIGINT_MATH -> JMLModifier.CODE_BIGINT_MATH;
        default -> throw new IllegalStateException("Illegal token is given");
        };
    }

    public TextualTranslator(boolean attachOriginLabel) {
        this.attachOriginLabel = attachOriginLabel;
    }

    @Override
    public @Nullable Object visitModifier(JmlParser.@NonNull ModifierContext ctx) {
        mods = mods.append(modifierFromToken(ctx.mod));
        return null;
    }

    @Override
    public Object visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
        return super.visitMethodlevel_comment(ctx);
    }

    @Override
    public @Nullable Object visitSpec_case(JmlParser.@NonNull Spec_caseContext ctx) {
        // read contract modifier and behavior ID
        mods = ImmutableSLList.nil();
        if (ctx.modifiers() != null) {
            for (JmlParser.ModifierContext mod : ctx.modifiers().modifier()) {
                mods = mods.append(modifierFromToken(mod.mod));
            }
        }
        Behavior behaviour = getBehavior(ctx.behavior);

        methodContract = new TextualJMLSpecCase(mods, behaviour);
        loopContract = null;
        constructs = constructs.append(methodContract);
        super.visitSpec_body(ctx.spec_body());
        methodContract = null;
        return null;
    }

    private @NonNull Behavior getBehavior(@Nullable Token behavior) {
        if (behavior == null) {
            return Behavior.NONE; // lightweight specification
        }
        return switch (behavior.getType()) {
        case JmlLexer.BEHAVIOR -> Behavior.BEHAVIOR;
        case JmlLexer.NORMAL_BEHAVIOR -> Behavior.NORMAL_BEHAVIOR;
        case JmlLexer.BREAK_BEHAVIOR -> Behavior.BREAK_BEHAVIOR;
        case JmlLexer.EXCEPTIONAL_BEHAVIOUR -> Behavior.EXCEPTIONAL_BEHAVIOR;
        case JmlLexer.MODEL_BEHAVIOUR -> Behavior.MODEL_BEHAVIOR;
        case JmlLexer.RETURN_BEHAVIOR -> Behavior.RETURN_BEHAVIOR;
        case JmlLexer.CONTINUE_BEHAVIOR -> Behavior.CONTINUE_BEHAVIOR;
        default -> throw new IllegalStateException("No behavior is given");
        };
    }

    @Override
    public @Nullable Object visitSpec_body(JmlParser.@NonNull Spec_bodyContext ctx) {
        acceptAll(ctx.a);
        if (ctx.NEST_START() != null) {
            final TextualJMLSpecCase base = methodContract;
            if (ctx.inner != null) {
                assert base != null;
                methodContract = base.clone();
                constructs = constructs.append(methodContract);
                acceptAll(ctx.inner);
            }

            for (JmlParser.Spec_bodyContext it : ctx.spec_body()) {
                assert base != null;
                methodContract = base.clone();
                constructs = constructs.append(methodContract);
                accept(it);
            }
        }
        return null;
    }

    @Override
    public Name @NonNull [] visitTargetHeap(JmlParser.@Nullable TargetHeapContext ctx) {
        if (ctx == null || ctx.SPECIAL_IDENT().isEmpty()) {
            return new Name[] { HeapLDT.BASE_HEAP_NAME };
        }
        Name[] heaps = new Name[ctx.SPECIAL_IDENT().size()];
        for (int i = 0; i < ctx.SPECIAL_IDENT().size(); i++) {
            String t = ctx.SPECIAL_IDENT(i).getText();
            heaps[i] = new Name(t.substring(1, t.length() - 1));
        }
        return heaps;
    }

    @Override
    public @Nullable Object visitEnsures_clause(JmlParser.@NonNull Ensures_clauseContext ctx) {
        assert methodContract != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final boolean isFree = ctx.ENSURES().getText().endsWith("_free");
        final LabeledParserRuleContext ctx2 =
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                isFree ? OriginTermLabel.SpecType.ENSURES_FREE : OriginTermLabel.SpecType.ENSURES,
                attachOriginLabel);
        for (Name heap : heaps) {
            methodContract.addClause(isFree ? ENSURES_FREE : ENSURES, heap, ctx2);
        }
        return null;
    }

    @Override
    public @Nullable Object visitRequires_clause(JmlParser.@NonNull Requires_clauseContext ctx) {
        assert methodContract != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            final boolean isFree = ctx.REQUIRES().getText().endsWith("_free");

            LabeledParserRuleContext ctx2 =
                LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                    isFree ? OriginTermLabel.SpecType.REQUIRES_FREE
                            : OriginTermLabel.SpecType.REQUIRES,
                    attachOriginLabel);

            methodContract.addClause(isFree ? REQUIRES_FREE : REQUIRES, heap, ctx2);
        }
        return null;
    }

    @Override
    public @Nullable Object visitMeasured_by_clause(JmlParser.@NonNull Measured_by_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(MEASURED_BY,
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.MEASURED_BY, attachOriginLabel));
        return null;
    }

    @Override
    public Object visitCaptures_clause(JmlParser.Captures_clauseContext ctx) {
        raiseError("Captures clauses are not supported by KeY.", ctx);
        return null;
    }

    @Override
    public @Nullable Object visitDiverges_clause(JmlParser.@NonNull Diverges_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(DIVERGES, ctx);
        return null;
    }

    @Override
    public Object visitWorking_space_clause(JmlParser.Working_space_clauseContext ctx) {
        raiseError("working space clauses are not supported by KeY.", ctx);
        return null;
    }

    @Override
    public Object visitDuration_clause(JmlParser.Duration_clauseContext ctx) {
        raiseError("Duration clauses are not supported by KeY.", ctx);
        return null;
    }

    @Override
    public Object visitWhen_clause(JmlParser.When_clauseContext ctx) {
        raiseError("When clauses are not supported by KeY.", ctx);
        return null;
    }

    @Override
    public @Nullable Object visitAccessible_clause(JmlParser.@NonNull Accessible_clauseContext ctx) {
        assert methodContract != null;
        boolean depends = ctx.MEASURED_BY() != null || ctx.COLON() != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final LabeledParserRuleContext ctx2 =
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.ACCESSIBLE, attachOriginLabel);
        for (Name heap : heaps) {
            if (depends) {
                TextualJMLDepends d = new TextualJMLDepends(mods, heaps, ctx2);
                constructs = constructs.append(d);
            } else if (methodContract != null) {
                methodContract.addClause(ACCESSIBLE, heap, ctx2);
            } else {
                assert false;
            }
        }
        return null;
    }

    @Override
    public @Nullable Object visitAssignable_clause(JmlParser.@NonNull Assignable_clauseContext ctx) {
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final boolean isFree =
            ctx.ASSIGNABLE() != null && ctx.ASSIGNABLE().getText().endsWith("_free");
        final LabeledParserRuleContext ctx2 =
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx, isFree
                    ? OriginTermLabel.SpecType.ASSIGNABLE_FREE
                    : OriginTermLabel.SpecType.ASSIGNABLE,
                attachOriginLabel);
        for (Name heap : heaps) {
            if (methodContract != null) {
                methodContract.addClause(isFree ? ASSIGNABLE_FREE : ASSIGNABLE, heap, ctx2);
            }
            if (loopContract != null) {
                loopContract.addClause(
                    isFree ? TextualJMLLoopSpec.ClauseHd.ASSIGNABLE_FREE
                            : TextualJMLLoopSpec.ClauseHd.ASSIGNABLE,
                    heap, ctx2);
            }
        }
        return null;
    }

    @Override
    public @Nullable Object visitLoop_assignable_clause(JmlParser.@NonNull Loop_assignable_clauseContext ctx) {
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final boolean isFree =
            (ctx.LOOP_ASSIGNABLE() != null && ctx.LOOP_ASSIGNABLE().getText().endsWith("_free"))
                    || (ctx.ASSIGNABLE() != null && ctx.ASSIGNABLE().getText().endsWith("_free"));
        final LabeledParserRuleContext ctx2 =
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx, isFree
                    ? OriginTermLabel.SpecType.ASSIGNABLE_FREE
                    : OriginTermLabel.SpecType.ASSIGNABLE,
                attachOriginLabel);
        for (Name heap : heaps) {
            if (loopContract != null) {
                loopContract.addClause(
                    isFree ? TextualJMLLoopSpec.ClauseHd.ASSIGNABLE_FREE
                            : TextualJMLLoopSpec.ClauseHd.ASSIGNABLE,
                    heap, ctx2);
            }
        }
        return null;
    }

    @Override
    public @Nullable Object visitVariant_function(JmlParser.@NonNull Variant_functionContext ctx) {
        final LabeledParserRuleContext ctx2 =
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.DECREASES, attachOriginLabel);
        if (loopContract != null) {
            loopContract.setVariant(ctx2);
        } else {
            assert methodContract != null;
            methodContract.addClause(DECREASES, ctx2);
        }
        return null;
    }

    @Override
    public @Nullable Object visitInitially_clause(JmlParser.@NonNull Initially_clauseContext ctx) {
        TextualJMLInitially initially =
            new TextualJMLInitially(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(initially);
        return null;
    }

    @Override
    public Object visitRepresents_clause(JmlParser.@NonNull Represents_clauseContext ctx) {
        TextualJMLRepresents represents =
            new TextualJMLRepresents(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(represents);
        return super.visitRepresents_clause(ctx);
    }

    @Override
    public @Nullable Object visitSeparates_clause(JmlParser.@NonNull Separates_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(INFORMATION_FLOW, ctx);
        return null;
    }

    @Override
    public @Nullable Object visitLoop_separates_clause(JmlParser.@NonNull Loop_separates_clauseContext ctx) {
        assert loopContract != null;
        loopContract.addClause(TextualJMLLoopSpec.ClauseHd.INFORMATION_FLOW,
            new LabeledParserRuleContext(ctx));
        return null;
    }

    @Override
    public @Nullable Object visitDetermines_clause(JmlParser.@NonNull Determines_clauseContext ctx) {
        if (methodContract != null) {
            methodContract.addClause(INFORMATION_FLOW, ctx);
        } else if (loopContract != null) {
            loopContract.addClause(TextualJMLLoopSpec.ClauseHd.INFORMATION_FLOW,
                HeapLDT.BASE_HEAP_NAME, new LabeledParserRuleContext(ctx));
        }
        return null;
    }

    @Override
    public Object visitLoop_determines_clause(JmlParser.Loop_determines_clauseContext ctx) {
        raiseError("Loop determines clauses are not supported by KeY.", ctx);
        return null;
    }

    @Override
    public @NonNull Object visitSignals_clause(JmlParser.@NonNull Signals_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(SIGNALS,
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.SIGNALS, attachOriginLabel));
        return this;
    }

    @Override
    public @Nullable Object visitSignals_only_clause(JmlParser.@NonNull Signals_only_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(SIGNALS_ONLY,
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.SIGNALS_ONLY, attachOriginLabel));
        return null;
    }

    @Override
    public @Nullable Object visitBreaks_clause(JmlParser.@NonNull Breaks_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(BREAKS,
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.BREAKS, attachOriginLabel));
        return null;
    }

    @Override
    public @Nullable Object visitContinues_clause(JmlParser.@NonNull Continues_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(CONTINUES,
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.CONTINUES, attachOriginLabel));
        return null;
    }

    @Override
    public @Nullable Object visitReturns_clause(JmlParser.@NonNull Returns_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(RETURNS,
            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                OriginTermLabel.SpecType.RETURNS, attachOriginLabel));
        return null;
    }

    @Override
    public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
        raiseError("Name clauses are not supported by KeY.", ctx);
        return null;
    }

    private void acceptAll(@NonNull Iterable<? extends ParserRuleContext> ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            accept(ctx);
        }
    }

    @SuppressWarnings("unchecked")
    private <T> T accept(@Nullable ParserRuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        return (T) ctx.accept(this);
    }

    @Override
    public Object visitMethodlevel_element(JmlParser.Methodlevel_elementContext ctx) {
        return super.visitMethodlevel_element(ctx);
    }

    @Override
    public Object visitModifiers(JmlParser.ModifiersContext ctx) {
        mods = ImmutableSLList.nil();
        return super.visitModifiers(ctx);
    }

    @Override
    public @Nullable Object visitClass_invariant(JmlParser.@NonNull Class_invariantContext ctx) {
        final boolean isFree = ctx.INVARIANT().getText().endsWith("_free");
        TextualJMLClassInv inv = new TextualJMLClassInv(mods, ctx, isFree);
        constructs = constructs.append(inv);
        return null;
    }

    @Override
    public @Nullable Object visitClass_axiom(JmlParser.@NonNull Class_axiomContext ctx) {
        TextualJMLClassAxiom inv =
            new TextualJMLClassAxiom(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(inv);
        return null;
    }


    @Override
    public @Nullable Object visitField_declaration(JmlParser.@NonNull Field_declarationContext ctx) {
        assert !mods.isEmpty();
        TextualJMLFieldDecl inv = new TextualJMLFieldDecl(mods, ctx);
        constructs = constructs.append(inv);
        return null;
    }


    @Override
    public @Nullable Object visitMethod_declaration(JmlParser.@NonNull Method_declarationContext ctx) {
        TextualJMLMethodDecl decl = new TextualJMLMethodDecl(mods, ctx);
        constructs = constructs.append(decl);
        return null;
    }

    @Override
    public @Nullable Object visitSet_statement(JmlParser.@NonNull Set_statementContext ctx) {
        TextualJMLSetStatement inv = new TextualJMLSetStatement(mods, ctx);
        constructs = constructs.append(inv);
        return null;
    }

    @Override
    public @Nullable Object visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
        loopContract = new TextualJMLLoopSpec(mods);
        methodContract = null;
        constructs = constructs.append(loopContract);
        super.visitLoop_specification(ctx);
        loopContract = null;
        return null;
    }

    @Override
    public @Nullable Object visitMerge_point_statement(JmlParser.@NonNull Merge_point_statementContext ctx) {
        TextualJMLMergePointDecl mergePointDecl = new TextualJMLMergePointDecl(mods, ctx);
        constructs = constructs.append(mergePointDecl);
        return null;
    }

    @Override
    public @Nullable Object visitLoop_invariant(JmlParser.@NonNull Loop_invariantContext ctx) {
        assert loopContract != null;
        final boolean isFree = ctx.LOOP_INVARIANT().getText().endsWith("_free");
        TextualJMLLoopSpec.ClauseHd type = isFree ? INVARIANT_FREE : INVARIANT;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            loopContract.addClause(type, heap,
                LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                    isFree ? OriginTermLabel.SpecType.LOOP_INVARIANT_FREE
                            : OriginTermLabel.SpecType.LOOP_INVARIANT,
                    attachOriginLabel));
        }
        return null;
    }


    @Override
    public @Nullable Object visitAssume_statement(JmlParser.@NonNull Assume_statementContext ctx) {
        TextualJMLAssertStatement b =
            new TextualJMLAssertStatement(TextualJMLAssertStatement.Kind.ASSUME,
                new KeyAst.Expression(ctx.expression()));
        constructs = constructs.append(b);
        return null;
    }


    @Override
    public @Nullable Object visitAssert_statement(JmlParser.@NonNull Assert_statementContext ctx) {
        TextualJMLAssertStatement b = new TextualJMLAssertStatement(
            TextualJMLAssertStatement.Kind.ASSERT, new KeyAst.Expression(ctx.expression()));
        constructs = constructs.append(b);
        return null;
    }

    @Override
    public @Nullable Object visitBlock_specification(JmlParser.@NonNull Block_specificationContext ctx) {
        accept(ctx.method_specification());
        return null;
    }

    @Override
    public @Nullable Object visitBlock_loop_specification(JmlParser.@NonNull Block_loop_specificationContext ctx) {
        acceptAll(ctx.spec_case());
        for (TextualJMLConstruct construct : constructs) {
            construct.setLoopContract(true);
        }
        return null;
    }
}
