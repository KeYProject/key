package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.annotation.Nullable;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT_FREE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.*;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;
import static de.uka.ilkd.key.speclang.njml.Translator.raiseError;

class TextualTranslator extends JmlParserBaseVisitor<Object> {
    public ImmutableList<TextualJMLConstruct> constructs = ImmutableSLList.nil();
    private ImmutableList<JMLModifier> mods = ImmutableSLList.nil();
    @Nullable
    private TextualJMLSpecCase methodContract;
    @Nullable
    private TextualJMLLoopSpec loopContract;

    /**
     * Translates a token to a JMLModifier
     *
     * @param token the token
     * @return the modifier
     */
    public static JMLModifier modifierFromToken(Token token) {
        if (token == null) {
            return null;
        }

        switch (token.getType()) {
        case JmlLexer.ABSTRACT:
            return JMLModifier.ABSTRACT;
        case JmlLexer.FINAL:
            return JMLModifier.FINAL;
        case JmlLexer.GHOST:
            return JMLModifier.GHOST;
        case JmlLexer.HELPER:
            return JMLModifier.HELPER;
        case JmlLexer.INSTANCE:
            return JMLModifier.INSTANCE;
        case JmlLexer.MODEL:
            return JMLModifier.MODEL;
        case JmlLexer.NON_NULL:
            return JMLModifier.NON_NULL;
        case JmlLexer.NULLABLE:
            return JMLModifier.NULLABLE;
        case JmlLexer.NULLABLE_BY_DEFAULT:
            return JMLModifier.NULLABLE_BY_DEFAULT;
        case JmlLexer.PRIVATE:
            return JMLModifier.PRIVATE;
        case JmlLexer.PROTECTED:
            return JMLModifier.PROTECTED;
        case JmlLexer.PUBLIC:
            return JMLModifier.PUBLIC;
        case JmlLexer.PURE:
            return JMLModifier.PURE;
        case JmlLexer.STRICTLY_PURE:
            return JMLModifier.STRICTLY_PURE;
        case JmlLexer.SPEC_PROTECTED:
            return JMLModifier.SPEC_PROTECTED;
        case JmlLexer.SPEC_PUBLIC:
            return JMLModifier.SPEC_PUBLIC;
        case JmlLexer.STATIC:
            return JMLModifier.STATIC;
        case JmlLexer.TWO_STATE:
            return JMLModifier.TWO_STATE;
        case JmlLexer.NO_STATE:
            return JMLModifier.NO_STATE;
        case JmlLexer.SPEC_JAVA_MATH:
            return JMLModifier.SPEC_JAVA_MATH;
        case JmlLexer.SPEC_SAFE_MATH:
            return JMLModifier.SPEC_SAFE_MATH;
        case JmlLexer.SPEC_BIGINT_MATH:
            return JMLModifier.SPEC_BIGINT_MATH;
        case JmlLexer.CODE_JAVA_MATH:
            return JMLModifier.CODE_JAVA_MATH;
        case JmlLexer.CODE_SAFE_MATH:
            return JMLModifier.CODE_SAFE_MATH;
        case JmlLexer.CODE_BIGINT_MATH:
            return JMLModifier.CODE_BIGINT_MATH;
        }
        throw new IllegalStateException("Illegal token is given");
    }

    @Override
    public Object visitModifier(JmlParser.ModifierContext ctx) {
        mods = mods.append(modifierFromToken(ctx.mod));
        return null;
    }

    @Override
    public Object visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
        return super.visitMethodlevel_comment(ctx);
    }

    @Override
    public Object visitSpec_case(JmlParser.Spec_caseContext ctx) {
        Behavior behaviour = getBehavior(ctx.behavior);
        methodContract = new TextualJMLSpecCase(mods, behaviour);
        loopContract = null;
        constructs = constructs.append(methodContract);
        super.visitSpec_case(ctx);
        methodContract = null;
        return null;
    }

    private Behavior getBehavior(Token behavior) {
        if (behavior == null) {
            return Behavior.NONE; // lightweight specification
        }

        switch (behavior.getType()) {
        case JmlLexer.BEHAVIOR:
            return Behavior.BEHAVIOR;
        case JmlLexer.NORMAL_BEHAVIOR:
            return Behavior.NORMAL_BEHAVIOR;
        case JmlLexer.BREAK_BEHAVIOR:
            return Behavior.BREAK_BEHAVIOR;
        case JmlLexer.EXCEPTIONAL_BEHAVIOUR:
            return Behavior.EXCEPTIONAL_BEHAVIOR;
        case JmlLexer.MODEL_BEHAVIOUR:
            return Behavior.MODEL_BEHAVIOR;
        case JmlLexer.RETURN_BEHAVIOR:
            return Behavior.RETURN_BEHAVIOR;
        case JmlLexer.CONTINUE_BEHAVIOR:
            return Behavior.CONTINUE_BEHAVIOR;
        }
        throw new IllegalStateException("No behavior is given");
    }

    @Override
    public Object visitSpec_body(JmlParser.Spec_bodyContext ctx) {
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
    public Name[] visitTargetHeap(JmlParser.TargetHeapContext ctx) {
        if (ctx == null || ctx.SPECIAL_IDENT().size() == 0) {
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
    public Object visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
        assert methodContract != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final boolean isFree = ctx.ENSURES().getText().endsWith("_free");
        final LabeledParserRuleContext ctx2 = new LabeledParserRuleContext(ctx,
            isFree ? OriginTermLabel.SpecType.ENSURES_FREE : OriginTermLabel.SpecType.ENSURES);
        for (Name heap : heaps) {
            methodContract.addClause(isFree ? ENSURES_FREE : ENSURES, heap, ctx2);
        }
        return null;
    }

    @Override
    public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        assert methodContract != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            final boolean isFree = ctx.REQUIRES().getText().endsWith("_free");
            LabeledParserRuleContext ctx2 =
                new LabeledParserRuleContext(ctx, isFree ? OriginTermLabel.SpecType.REQUIRES_FREE
                        : OriginTermLabel.SpecType.REQUIRES);
            methodContract.addClause(isFree ? REQUIRES_FREE : REQUIRES, heap, ctx2);
        }
        return null;
    }

    @Override
    public Object visitMeasured_by_clause(JmlParser.Measured_by_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(MEASURED_BY,
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.MEASURED_BY));
        return null;
    }

    @Override
    public Object visitCaptures_clause(JmlParser.Captures_clauseContext ctx) {
        raiseError("Captures clauses are not supported by KeY.", ctx);
        return null;
    }

    @Override
    public Object visitDiverges_clause(JmlParser.Diverges_clauseContext ctx) {
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
    public Object visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
        assert methodContract != null;
        boolean depends = ctx.MEASURED_BY() != null || ctx.COLON() != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final LabeledParserRuleContext ctx2 =
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.ACCESSIBLE);
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
    public Object visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        final LabeledParserRuleContext ctx2 =
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.ASSIGNABLE);
        for (Name heap : heaps) {
            if (methodContract != null) {
                methodContract.addClause(ASSIGNABLE, heap, ctx2);
            }
            if (loopContract != null) {
                loopContract.addClause(TextualJMLLoopSpec.ClauseHd.ASSIGNABLE, heap, ctx2);
            }
        }
        return null;
    }

    @Override
    public Object visitVariant_function(JmlParser.Variant_functionContext ctx) {
        final LabeledParserRuleContext ctx2 =
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.DECREASES);
        if (loopContract != null) {
            loopContract.setVariant(ctx2);
        } else {
            assert methodContract != null;
            methodContract.addClause(DECREASES, ctx2);
        }
        return null;
    }

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        TextualJMLInitially initially =
            new TextualJMLInitially(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(initially);
        return null;
    }

    @Override
    public Object visitRepresents_clause(JmlParser.Represents_clauseContext ctx) {
        TextualJMLRepresents represents =
            new TextualJMLRepresents(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(represents);
        return super.visitRepresents_clause(ctx);
    }

    @Override
    public Object visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(INFORMATION_FLOW, ctx);
        return null;
    }

    @Override
    public Object visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
        assert loopContract != null;
        loopContract.addClause(TextualJMLLoopSpec.ClauseHd.INFORMATION_FLOW,
            new LabeledParserRuleContext(ctx));
        return null;
    }

    @Override
    public Object visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
        if (methodContract != null)
            methodContract.addClause(INFORMATION_FLOW, ctx);
        else if (loopContract != null) {
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
    public Object visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(SIGNALS,
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.SIGNALS));
        return this;
    }

    @Override
    public Object visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(SIGNALS_ONLY,
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.SIGNALS_ONLY));
        return null;
    }

    @Override
    public Object visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(BREAKS,
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.BREAKS));
        return null;
    }

    @Override
    public Object visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(CONTINUES,
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.CONTINUES));
        return null;
    }

    @Override
    public Object visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(RETURNS,
            new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.RETURNS));
        return null;
    }

    @Override
    public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
        raiseError("Name clauses are not supported by KeY.", ctx);
        return null;
    }

    private void acceptAll(Iterable<? extends ParserRuleContext> ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            accept(ctx);
        }
    }

    @SuppressWarnings("unchecked")
    private <T> T accept(ParserRuleContext ctx) {
        if (ctx == null)
            return null;
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
    public Object visitClass_invariant(JmlParser.Class_invariantContext ctx) {
        TextualJMLClassInv inv = new TextualJMLClassInv(mods, ctx);
        constructs = constructs.append(inv);
        return null;
    }

    @Override
    public Object visitClass_axiom(JmlParser.Class_axiomContext ctx) {
        TextualJMLClassAxiom inv =
            new TextualJMLClassAxiom(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(inv);
        return null;
    }


    @Override
    public Object visitField_declaration(JmlParser.Field_declarationContext ctx) {
        assert mods.size() > 0;
        TextualJMLFieldDecl inv = new TextualJMLFieldDecl(mods, ctx);
        constructs = constructs.append(inv);
        return null;
    }


    @Override
    public Object visitMethod_declaration(JmlParser.Method_declarationContext ctx) {
        TextualJMLMethodDecl decl = new TextualJMLMethodDecl(mods, ctx);
        constructs = constructs.append(decl);
        return null;
    }

    @Override
    public Object visitSet_statement(JmlParser.Set_statementContext ctx) {
        TextualJMLSetStatement inv = new TextualJMLSetStatement(mods, ctx);
        constructs = constructs.append(inv);
        return null;
    }

    @Override
    public Object visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
        loopContract = new TextualJMLLoopSpec(mods);
        methodContract = null;
        constructs = constructs.append(loopContract);
        super.visitLoop_specification(ctx);
        loopContract = null;
        return null;
    }

    @Override
    public Object visitMerge_point_statement(JmlParser.Merge_point_statementContext ctx) {
        TextualJMLMergePointDecl mergePointDecl = new TextualJMLMergePointDecl(mods, ctx);
        constructs = constructs.append(mergePointDecl);
        return null;
    }

    @Override
    public Object visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
        assert loopContract != null;
        final boolean isFree = ctx.LOOP_INVARIANT().getText().endsWith("_free");
        TextualJMLLoopSpec.ClauseHd type = isFree ? INVARIANT_FREE : INVARIANT;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            loopContract.addClause(type, heap,
                new LabeledParserRuleContext(ctx,
                    isFree ? OriginTermLabel.SpecType.LOOP_INVARIANT_FREE
                            : OriginTermLabel.SpecType.LOOP_INVARIANT));
        }
        return null;
    }


    @Override
    public Object visitAssume_statement(JmlParser.Assume_statementContext ctx) {
        TextualJMLAssertStatement b =
            new TextualJMLAssertStatement(TextualJMLAssertStatement.Kind.ASSUME,
                new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.ASSUME));
        constructs = constructs.append(b);
        return null;
    }


    @Override
    public Object visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        TextualJMLAssertStatement b =
            new TextualJMLAssertStatement(TextualJMLAssertStatement.Kind.ASSERT,
                new LabeledParserRuleContext(ctx, OriginTermLabel.SpecType.ASSERT));
        constructs = constructs.append(b);
        return null;
    }

    @Override
    public Object visitBlock_specification(JmlParser.Block_specificationContext ctx) {
        accept(ctx.method_specification());
        return null;
    }

    @Override
    public Object visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
        acceptAll(ctx.spec_case());
        for (TextualJMLConstruct construct : constructs) {
            construct.setLoopContract(true);
        }
        return null;
    }
}
