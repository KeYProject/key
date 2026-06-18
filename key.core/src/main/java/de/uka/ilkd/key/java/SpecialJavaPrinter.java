/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.JmlParserBaseVisitor;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.printer.DefaultPrettyPrinterVisitor;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.google.common.base.Strings;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jspecify.annotations.Nullable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/30/26)
 */
public class SpecialJavaPrinter extends DefaultPrettyPrinterVisitor {
    public SpecialJavaPrinter(PrinterConfiguration configuration) {
        super(configuration);
    }

    @Override
    public void visit(Modifier n, Void arg) {
        var isJML = false;
        if (n.getKeyword() instanceof Modifier.DefaultKeyword kw) {
            isJML = kw.toString().startsWith("JML_");
        } else {
            isJML = true;
        }

        if (isJML) {
            printer.print("/*@ ");
            printer.print(n.getKeyword().asString());
            printer.print("*/ ");
        } else {
            super.visit(n, arg);
        }
    }

    @Override
    public void visit(MethodDeclaration n, Void arg) {
        print(TransformationPipelineServices.getSpec(n));
        super.visit(n, arg);
    }

    @Override
    public void visit(ConstructorDeclaration n, Void arg) {
        print(TransformationPipelineServices.getSpec(n));
        super.visit(n, arg);
    }

    @Override
    protected void printCompactClassMembers(NodeList<BodyDeclaration<?>> members, Void arg) {
        print(TransformationPipelineServices.getClassSpec(members.getParentNode().get()));
        super.printCompactClassMembers(members, arg);
    }

    @Override
    protected void printMembers(NodeList<BodyDeclaration<?>> members, Void arg) {
        print(TransformationPipelineServices.getClassSpec(members.getParentNode().get()));
        super.printMembers(members, arg);
    }


    private void print(List<TextualJMLConstruct> spec) {
        for (var construct : spec) {
            switch (construct) {
                case TextualJMLLoopSpec c -> print(c);
                case TextualJMLAssertStatement c -> print(c);
                case TextualJMLClassAxiom c -> print(c.getModifiers(), c.getAxiom().first);
                case TextualJMLClassInv c -> print(c.getModifiers(), c.getInv());
                case TextualJMLDepends c -> print(c.getModifiers(), c.getDepends());
                case TextualJMLFieldDecl c -> {
                }
                case TextualJMLInitially c -> print(c.getModifiers(), c.getInv().first);
                case TextualJMLMergePointDecl c -> print(c.getModifiers(), c.getMergeProc());
                case TextualJMLMethodDecl c -> print(c.getModifiers(), c.getDecl());
                case TextualJMLModifierList c -> print(c.getModifiers());
                case TextualJMLRepresents c -> print(c.getModifiers(), c.getRepresents().first);
                case TextualJMLSetStatement c -> print(c.getAssignment());
                case TextualJMLSpecCase c -> print(c.getModifiers(), c);
                default -> throw new IllegalStateException("Unexpected value: " + construct);
            }
        }
    }

    private void print(ImmutableList<JMLModifier> modifiers,
            ImmutableList<LabeledParserRuleContext> depends) {
        printer.print("\n/*@ ");
        print(modifiers);
        printer.print(" ");
        depends.forEach(it -> printer.print(it.first.accept(new ToStringVisitor()) + "\n"));
        printer.print("*/\n");
    }

    private void print(ImmutableList<JMLModifier> modifiers, TextualJMLSpecCase specCase) {
        printer.print("/*");
        printer.reindentWithAlignToCursor();
        printer.print("@ ");
        print(modifiers);
        printer.print(" ");
        printer.print(specCase.getBehavior().toString());
        printer.println();
        specCase.getClauses().forEach(it -> {
            printer.println("@ " + it.accept(new ToStringVisitor()));
        });
        printer.println();
        printer.println("@*/");
        printer.reindentToPreviousLevel();
    }


    private void print(ImmutableList<JMLModifier> modifiers, @Nullable ParserRuleContext first) {
        if (first == null)
            return;
        var text = first.accept(new ToStringVisitor());
        if (text.contains("\n")) {
            printer.print("/*@ ");
            print(modifiers);
            printer.print(text);
            printer.print("\n*/");
        } else {
            printer.print("//@ ");
            print(modifiers);
            printer.println(text);
        }
    }

    private void print(ImmutableList<JMLModifier> modifiers) {
        for (var modifier : modifiers) {
            printer.print(modifier.getParserKeyword().asString());
            printer.print(" ");
        }
    }

    private void print(@Nullable ParserRuleContext first) {
        if (first == null)
            return;
        var text = first.accept(new ToStringVisitor());
        if (text.contains("\n")) {
            printer.print("/*@ ");
            printer.print(text);
            printer.print("\n*/");
        } else {
            printer.print("//@ ");
            printer.print(text);
        }
    }

    private void print(TextualJMLAssertStatement c) {
        printer.print("//@ assert " + c.getContext().accept(new ToStringVisitor()) + ";\n");
    }

    private void print(TextualJMLLoopSpec specCase) {
        printer.print("/*@ ");
        print(specCase.getModifiers());
        printer.print(" ");
        specCase.getClauses().forEach(it -> printer.print(it.accept(new ToStringVisitor()) + "\n"));
        printer.print("\n*/");
    }
}


class ToStringVisitor extends JmlParserBaseVisitor<String> {
    @Override
    public String visitTerminal(TerminalNode node) {
        return node.getText();
    }

    public String accept(@Nullable ParseTree ctx) {
        if (ctx == null)
            return "";
        return ctx.accept(this);
    }

    public String accept(String prefix, @Nullable ParseTree c) {
        if (c == null)
            return "";
        return prefix + c.accept(this);
    }

    public String accept(@Nullable ParseTree c, String suffix) {
        if (c == null)
            return "";
        return c.accept(this) + suffix;
    }

    @Override
    public String visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
        return "accessible " + accept(ctx.targetHeap())
            + accept(ctx.lhs, ":")
            + accept(ctx.rhs)
            + accept(" \\measured_by ", ctx.mby)
            + ";";
    }

    @Override
    public String visitAdditiveexpr(JmlParser.AdditiveexprContext ctx) {
        return accept(ctx.multexpr(), ctx.op);
    }

    @Override
    public String visitAlso_keyword(JmlParser.Also_keywordContext ctx) {
        return super.visitAlso_keyword(ctx);
    }

    @Override
    public String visitAndexpr(JmlParser.AndexprContext ctx) {
        return accept(ctx.equalityexpr(), " & ");
    }

    @Override
    public String visitArray_dimension(JmlParser.Array_dimensionContext ctx) {
        return super.visitArray_dimension(ctx);
    }

    @Override
    public String visitArray_dimensions(JmlParser.Array_dimensionsContext ctx) {
        return super.visitArray_dimensions(ctx);
    }

    @Override
    public String visitArray_initializer(JmlParser.Array_initializerContext ctx) {
        return super.visitArray_initializer(ctx);
    }

    @Override
    public String visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        return super.visitAssert_statement(ctx);
    }

    @Override
    public String visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        return "assignable " + accept(ctx.targetHeap())
            + accept(ctx.storeRefUnion())
            + accept(ctx.STRICTLY_NOTHING())
            + ";";
    }

    private String accept(TerminalNode terminalNode) {
        if (terminalNode != null)
            return terminalNode.getText();
        return "";
    }

    @Override
    public String visitAssume_statement(JmlParser.Assume_statementContext ctx) {
        return super.visitAssume_statement(ctx);
    }

    @Override
    public String visitBeforeexpression(JmlParser.BeforeexpressionContext ctx) {
        return super.visitBeforeexpression(ctx);
    }

    @Override
    public String visitBigint_math_expression(JmlParser.Bigint_math_expressionContext ctx) {
        return "\\bigint_math(" + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
        return super.visitBlock_loop_specification(ctx);
    }

    @Override
    public String visitBlock_specification(JmlParser.Block_specificationContext ctx) {
        return super.visitBlock_specification(ctx);
    }

    @Override
    public String visitBoundvarmodifiers(JmlParser.BoundvarmodifiersContext ctx) {
        return ctx.start.getText();
    }

    @Override
    public String visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        return super.visitBreaks_clause(ctx);
    }

    @Override
    public String visitBsumterm(JmlParser.BsumtermContext ctx) {
        return "(\\bsum "
            + accept(ctx.quantifiedvardecls()) + "; "
            + accept(ctx.expression(), "; ")
            + ")";
    }

    @Override
    public String visitBuiltintype(JmlParser.BuiltintypeContext ctx) {
        return ctx.start.getText();
    }

    @Override
    public String visitCaptures_clause(JmlParser.Captures_clauseContext ctx) {
        return "captures "
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitCastexpr(JmlParser.CastexprContext ctx) {
        return "(" + accept(ctx.typespec()) + ") " + accept(ctx.unaryexpr());
    }

    @Override
    public String visitCharliteral(JmlParser.CharliteralContext ctx) {
        return accept(ctx.CHAR_LITERAL());
    }

    @Override
    public String visitClass_axiom(JmlParser.Class_axiomContext ctx) {
        return "axiom " + accept(ctx.expression()) + ";";
    }

    @Override
    public String visitClass_invariant(JmlParser.Class_invariantContext ctx) {
        return "invariant " + accept(ctx.expression()) + ";";
    }

    @Override
    public String visitClause(JmlParser.ClauseContext ctx) {
        return super.visitClause(ctx);
    }

    @Override
    public String visitClauseEOF(JmlParser.ClauseEOFContext ctx) {
        return super.visitClauseEOF(ctx);
    }

    @Override
    public String visitConditionalexpr(JmlParser.ConditionalexprContext ctx) {
        return accept(ctx.equivalenceexpr())
                + (ctx.QUESTIONMARK() != null
                        ? accept("? ", ctx.conditionalexpr(0))
                                + accept(" : ", ctx.conditionalexpr(1))
                        : "");
    }

    @Override
    public String visitConstant(JmlParser.ConstantContext ctx) {
        return super.visitConstant(ctx);
    }

    @Override
    public String visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        return super.visitContinues_clause(ctx);
    }

    @Override
    public String visitCreateLocset(JmlParser.CreateLocsetContext ctx) {
        return super.visitCreateLocset(ctx);
    }

    @Override
    public String visitDatagroup_clause(JmlParser.Datagroup_clauseContext ctx) {
        return super.visitDatagroup_clause(ctx);
    }

    @Override
    public String visitDebug_statement(JmlParser.Debug_statementContext ctx) {
        return super.visitDebug_statement(ctx);
    }

    @Override
    public String visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
        return super.visitDetermines_clause(ctx);
    }

    @Override
    public String visitDims(JmlParser.DimsContext ctx) {
        return Strings.repeat("[]", ctx.LBRACKET().size());
    }

    @Override
    public String visitDiverges_clause(JmlParser.Diverges_clauseContext ctx) {
        return "captures "
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitDuration_clause(JmlParser.Duration_clauseContext ctx) {
        return "duration "
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
        return "ensures " + accept(ctx.targetHeap())
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitEqualityexpr(JmlParser.EqualityexprContext ctx) {
        return accept(ctx.relationalexpr(), " == "); // TODO
    }

    @Override
    public String visitEquivalenceexpr(JmlParser.EquivalenceexprContext ctx) {
        return accept(ctx.impliesexpr(), "<==>"); // TODO
    }

    @Override
    public String visitExclusiveorexpr(JmlParser.ExclusiveorexprContext ctx) {
        return accept(ctx.andexpr(), " ^ ");
    }

    @Override
    public String visitExpression(JmlParser.ExpressionContext ctx) {
        return accept(ctx.conditionalexpr());
    }

    @Override
    public String visitExpressionEOF(JmlParser.ExpressionEOFContext ctx) {
        return super.visitExpressionEOF(ctx);
    }

    @Override
    public String visitExpressionlist(JmlParser.ExpressionlistContext ctx) {
        return accept(ctx.expression(), ", ");
    }

    @Override
    public String visitExprList(JmlParser.ExprListContext ctx) {
        return super.visitExprList(ctx);
    }

    @Override
    public String visitFalse_(JmlParser.False_Context ctx) {
        return super.visitFalse_(ctx);
    }

    @Override
    public String visitField_declaration(JmlParser.Field_declarationContext ctx) {
        return super.visitField_declaration(ctx);
    }

    @Override
    public String visitFpOperator(JmlParser.FpOperatorContext ctx) {
        return ctx.start.getText();
    }

    @Override
    public String visitFractionalliteral(JmlParser.FractionalliteralContext ctx) {
        return super.visitFractionalliteral(ctx);
    }

    @Override
    public String visitHistory_constraint(JmlParser.History_constraintContext ctx) {
        return super.visitHistory_constraint(ctx);
    }

    @Override
    public String visitIdent(JmlParser.IdentContext ctx) {
        return accept(ctx.children.getFirst());
    }

    @Override
    public String visitImpliesexpr(JmlParser.ImpliesexprContext ctx) {
        return accept(ctx.a)
                + accept(" ==> ", ctx.b)
                + accept(" <== ", ctx.c, " <== ");
    }

    @Override
    public String visitImpliesforwardexpr(JmlParser.ImpliesforwardexprContext ctx) {
        return accept(ctx.a) + accept(" ==> ", ctx.b);
    }

    @Override
    public String visitIn_group_clause(JmlParser.In_group_clauseContext ctx) {
        return super.visitIn_group_clause(ctx);
    }

    @Override
    public String visitInclusiveorexpr(JmlParser.InclusiveorexprContext ctx) {
        return accept(ctx.exclusiveorexpr(), " | ");
    }

    @Override
    public String visitInfflowspeclist(JmlParser.InfflowspeclistContext ctx) {
        return super.visitInfflowspeclist(ctx);
    }

    @Override
    public String visitInfinite_union_expr(JmlParser.Infinite_union_exprContext ctx) {
        return super.visitInfinite_union_expr(ctx);
    }

    @Override
    public String visitInitialiser(JmlParser.InitialiserContext ctx) {
        return super.visitInitialiser(ctx);
    }

    @Override
    public String visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        return "initially " + accept(ctx.expression()) + ";";
    }

    @Override
    public String visitInstance_of(JmlParser.Instance_ofContext ctx) {
        return accept(ctx.shiftexpr()) + " instanceof " + accept(ctx.typespec());
    }

    @Override
    public String visitIntegerliteral(JmlParser.IntegerliteralContext ctx) {
        return accept(ctx.BINLITERAL())
                + accept(ctx.DECLITERAL())
                + accept(ctx.HEXLITERAL())
                + accept(ctx.OCTLITERAL());
    }

    @Override
    public String visitInv(JmlParser.InvContext ctx) {
        return super.visitInv(ctx);
    }

    @Override
    public String visitInv_free(JmlParser.Inv_freeContext ctx) {
        return super.visitInv_free(ctx);
    }

    @Override
    public String visitJava_math_expression(JmlParser.Java_math_expressionContext ctx) {
        return "\\java_math("
            + accept(ctx.expression())
            + ")";
    }

    @Override
    public String visitJavaliteral(JmlParser.JavaliteralContext ctx) {
        return super.visitJavaliteral(ctx);
    }

    @Override
    public String visitLogicalandexpr(JmlParser.LogicalandexprContext ctx) {
        return accept(ctx.inclusiveorexpr(), " && ");
    }

    @Override
    public String visitLogicalorexpr(JmlParser.LogicalorexprContext ctx) {
        return accept(ctx.logicalandexpr(), " || ");
    }

    @Override
    public String visitLoop_assignable_clause(JmlParser.Loop_assignable_clauseContext ctx) {
        return super.visitLoop_assignable_clause(ctx);
    }

    @Override
    public String visitLoop_contract_keyword(JmlParser.Loop_contract_keywordContext ctx) {
        return super.visitLoop_contract_keyword(ctx);
    }

    @Override
    public String visitLoop_determines_clause(JmlParser.Loop_determines_clauseContext ctx) {
        return super.visitLoop_determines_clause(ctx);
    }

    @Override
    public String visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
        return super.visitLoop_invariant(ctx);
    }

    @Override
    public String visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
        return super.visitLoop_separates_clause(ctx);
    }

    @Override
    public String visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
        return super.visitLoop_specification(ctx);
    }

    @Override
    public String visitMapExpression(JmlParser.MapExpressionContext ctx) {
        return super.visitMapExpression(ctx);
    }

    @Override
    public String visitMaps_into_clause(JmlParser.Maps_into_clauseContext ctx) {
        return super.visitMaps_into_clause(ctx);
    }

    @Override
    public String visitMbody_block(JmlParser.Mbody_blockContext ctx) {
        return super.visitMbody_block(ctx);
    }

    @Override
    public String visitMbody_if(JmlParser.Mbody_ifContext ctx) {
        return super.visitMbody_if(ctx);
    }

    @Override
    public String visitMbody_return(JmlParser.Mbody_returnContext ctx) {
        return super.visitMbody_return(ctx);
    }

    @Override
    public String visitMbody_var(JmlParser.Mbody_varContext ctx) {
        return super.visitMbody_var(ctx);
    }

    @Override
    public String visitMeasured_by_clause(JmlParser.Measured_by_clauseContext ctx) {
        return "measured_by "
            + accept(ctx.predornot(), ", ")
            + ";";
    }

    private String accept(List<? extends ParseTree> ctxs, String s) {
        return ctxs.stream()
                .map(this::accept)
                .collect(Collectors.joining(s));
    }

    @Override
    public String visitMerge_point_statement(JmlParser.Merge_point_statementContext ctx) {
        return super.visitMerge_point_statement(ctx);
    }

    @Override
    public String visitMergeparamsspec(JmlParser.MergeparamsspecContext ctx) {
        return super.visitMergeparamsspec(ctx);
    }

    @Override
    public String visitMethod_declaration(JmlParser.Method_declarationContext ctx) {
        return super.visitMethod_declaration(ctx);
    }

    @Override
    public String visitMethod_specification(JmlParser.Method_specificationContext ctx) {
        return super.visitMethod_specification(ctx);
    }

    @Override
    public String visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
        return super.visitMethodlevel_comment(ctx);
    }

    @Override
    public String visitMethodlevel_element(JmlParser.Methodlevel_elementContext ctx) {
        return super.visitMethodlevel_element(ctx);
    }

    @Override
    public String visitModifier(JmlParser.ModifierContext ctx) {
        return super.visitModifier(ctx);
    }

    @Override
    public String visitModifiers(JmlParser.ModifiersContext ctx) {
        return super.visitModifiers(ctx);
    }

    @Override
    public String visitModifiersEOF(JmlParser.ModifiersEOFContext ctx) {
        return super.visitModifiersEOF(ctx);
    }

    @Override
    public String visitMonitors_for_clause(JmlParser.Monitors_for_clauseContext ctx) {
        return super.visitMonitors_for_clause(ctx);
    }

    @Override
    public String visitMultexpr(JmlParser.MultexprContext ctx) {
        return accept(ctx.unaryexpr(), ctx.op);
    }

    @Override
    public String visitName(JmlParser.NameContext ctx) {
        return ctx.ident().stream().map(this::accept).collect(Collectors.joining("."));
    }

    @Override
    public String visitName_clause(JmlParser.Name_clauseContext ctx) {
        return "name " + accept(ctx.SPEC_NAME());
    }

    @Override
    public String visitNew_expr(JmlParser.New_exprContext ctx) {
        return "new " + accept(ctx.type()) + "(" + accept(ctx.expressionlist(), ", ") + ")";
    }

    @Override
    public String visitNowarn_pragma(JmlParser.Nowarn_pragmaContext ctx) {
        return super.visitNowarn_pragma(ctx);
    }

    @Override
    public String visitNull_(JmlParser.Null_Context ctx) {
        return "null";
    }

    @Override
    public String visitOldexpression(JmlParser.OldexpressionContext ctx) {
        return "\\old(" + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitParam_decl(JmlParser.Param_declContext ctx) {
        return super.visitParam_decl(ctx);
    }

    @Override
    public String visitParam_list(JmlParser.Param_listContext ctx) {
        return super.visitParam_list(ctx);
    }

    @Override
    public String visitPignore1(JmlParser.Pignore1Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPignore2(JmlParser.Pignore2Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPignore3(JmlParser.Pignore3Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPignore4(JmlParser.Pignore4Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPignore5(JmlParser.Pignore5Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPignore6(JmlParser.Pignore6Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPignore7(JmlParser.Pignore7Context ctx) {
        return accept(ctx.getChild(0));
    }

    @Override
    public String visitPostfixexpr(JmlParser.PostfixexprContext ctx) {
        return accept(ctx.primaryexpr()) + accept(ctx.primarysuffix(), "");
    }

    @Override
    public String visitPredicate(JmlParser.PredicateContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public String visitPredornot(JmlParser.PredornotContext ctx) {
        return oneOf(ctx.predicate(), ctx.NOT_SPECIFIED());
    }

    @Override
    public String visitPrimaryAllFields(JmlParser.PrimaryAllFieldsContext ctx) {
        return super.visitPrimaryAllFields(ctx);
    }

    @Override
    public String visitPrimaryAllObj(JmlParser.PrimaryAllObjContext ctx) {
        return super.visitPrimaryAllObj(ctx);
    }

    @Override
    public String visitPrimaryBackup(JmlParser.PrimaryBackupContext ctx) {
        return super.visitPrimaryBackup(ctx);
    }

    @Override
    public String visitPrimaryBigintMathExpression(
            JmlParser.PrimaryBigintMathExpressionContext ctx) {
        return accept(ctx.bigint_math_expression());

    }

    @Override
    public String visitPrimaryCreateLocsetSingleton(
            JmlParser.PrimaryCreateLocsetSingletonContext ctx) {
        return super.visitPrimaryCreateLocsetSingleton(ctx);
    }

    @Override
    public String visitPrimaryDisjoint(JmlParser.PrimaryDisjointContext ctx) {
        return super.visitPrimaryDisjoint(ctx);
    }

    @Override
    public String visitPrimaryDuration(JmlParser.PrimaryDurationContext ctx) {
        return super.visitPrimaryDuration(ctx);
    }

    @Override
    public String visitPrimaryElemtype(JmlParser.PrimaryElemtypeContext ctx) {
        return super.visitPrimaryElemtype(ctx);
    }

    @Override
    public String visitPrimaryEmptySet(JmlParser.PrimaryEmptySetContext ctx) {
        return super.visitPrimaryEmptySet(ctx);
    }

    @Override
    public String visitPrimaryException(JmlParser.PrimaryExceptionContext ctx) {
        return super.visitPrimaryException(ctx);
    }

    @Override
    public String visitPrimaryexpr(JmlParser.PrimaryexprContext ctx) {
        return oneOf(ctx.children.getFirst());
    }

    private String oneOf(ParseTree... ctxs) {
        for (var ctx : ctxs) {
            if (ctx != null)
                return accept(ctx);
        }
        return "";
    }

    private String oneOf(TerminalNode... ctxs) {
        for (var ctx : ctxs) {
            if (ctx != null)
                return accept(ctx);
        }
        return "";
    }

    @Override
    public String visitPrimaryFresh(JmlParser.PrimaryFreshContext ctx) {
        return "\\fresh(" + accept(ctx.expressionlist()) + ")";
    }

    @Override
    public String visitPrimaryignore10(JmlParser.Primaryignore10Context ctx) {
        return super.visitPrimaryignore10(ctx);
    }

    @Override
    public String visitPrimaryIndex(JmlParser.PrimaryIndexContext ctx) {
        return super.visitPrimaryIndex(ctx);
    }

    @Override
    public String visitPrimaryInformalDesc(JmlParser.PrimaryInformalDescContext ctx) {
        return "(*" + accept(ctx.INFORMAL_DESCRIPTION()) + "*)";

    }

    @Override
    public String visitPrimaryIntersect(JmlParser.PrimaryIntersectContext ctx) {
        return "\\intersect(" + accept(ctx.storeRefIntersect()) + ")";
    }

    @Override
    public String visitPrimaryInvFor(JmlParser.PrimaryInvForContext ctx) {
        return "\\invariant_for(" + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitPrimaryInvFreeFor(JmlParser.PrimaryInvFreeForContext ctx) {
        return "\\free_invariant_for(" + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitPrimaryIsInitialised(JmlParser.PrimaryIsInitialisedContext ctx) {
        return super.visitPrimaryIsInitialised(ctx);
    }

    @Override
    public String visitPrimaryJavaMathExpression(JmlParser.PrimaryJavaMathExpressionContext ctx) {
        return super.visitPrimaryJavaMathExpression(ctx);
    }

    @Override
    public String visitPrimaryLblNeg(JmlParser.PrimaryLblNegContext ctx) {
        return "\\lblneg(" + accept(ctx.IDENT()) + ", " + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitPrimaryLblPos(JmlParser.PrimaryLblPosContext ctx) {
        return "\\lblpos(" + accept(ctx.IDENT()) + ", " + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitPrimaryLockset(JmlParser.PrimaryLocksetContext ctx) {
        return super.visitPrimaryLockset(ctx);
    }

    @Override
    public String visitPrimaryMapEmpty(JmlParser.PrimaryMapEmptyContext ctx) {
        return super.visitPrimaryMapEmpty(ctx);
    }

    @Override
    public String visitPrimaryMapExpr(JmlParser.PrimaryMapExprContext ctx) {
        return super.visitPrimaryMapExpr(ctx);
    }

    @Override
    public String visitPrimaryNewElemsfrehs(JmlParser.PrimaryNewElemsfrehsContext ctx) {
        return super.visitPrimaryNewElemsfrehs(ctx);
    }

    @Override
    public String visitPrimaryNNE(JmlParser.PrimaryNNEContext ctx) {
        return super.visitPrimaryNNE(ctx);
    }

    @Override
    public String visitPrimaryNotAssigned(JmlParser.PrimaryNotAssignedContext ctx) {
        return super.visitPrimaryNotAssigned(ctx);
    }

    @Override
    public String visitPrimaryNotMod(JmlParser.PrimaryNotModContext ctx) {
        return super.visitPrimaryNotMod(ctx);
    }

    @Override
    public String visitPrimaryParen(JmlParser.PrimaryParenContext ctx) {
        return "(" + accept(ctx.expression()) + ")";
    }

    @Override
    public String visitPrimaryPermission(JmlParser.PrimaryPermissionContext ctx) {
        return super.visitPrimaryPermission(ctx);
    }

    @Override
    public String visitPrimaryReach(JmlParser.PrimaryReachContext ctx) {
        return super.visitPrimaryReach(ctx);
    }

    @Override
    public String visitPrimaryReachLocs(JmlParser.PrimaryReachLocsContext ctx) {
        return super.visitPrimaryReachLocs(ctx);
    }

    @Override
    public String visitPrimaryResult(JmlParser.PrimaryResultContext ctx) {
        return "\\result";
    }

    @Override
    public String visitPrimarySafeMathExpression(JmlParser.PrimarySafeMathExpressionContext ctx) {
        return super.visitPrimarySafeMathExpression(ctx);
    }

    @Override
    public String visitPrimarySeq2Map(JmlParser.PrimarySeq2MapContext ctx) {
        return super.visitPrimarySeq2Map(ctx);
    }

    @Override
    public String visitPrimarySetMinux(JmlParser.PrimarySetMinuxContext ctx) {
        return super.visitPrimarySetMinux(ctx);
    }

    @Override
    public String visitPrimarySpace(JmlParser.PrimarySpaceContext ctx) {
        return super.visitPrimarySpace(ctx);
    }

    @Override
    public String visitPrimaryStaticInv(JmlParser.PrimaryStaticInvContext ctx) {
        return super.visitPrimaryStaticInv(ctx);
    }

    @Override
    public String visitPrimaryStaticInvFree(JmlParser.PrimaryStaticInvFreeContext ctx) {
        return super.visitPrimaryStaticInvFree(ctx);
    }

    @Override
    public String visitPrimaryStoreRef(JmlParser.PrimaryStoreRefContext ctx) {
        return ctx.start.getText() + " (" + accept(ctx.storeRefUnion()) + ")";
    }

    @Override
    public String visitPrimaryStringEq(JmlParser.PrimaryStringEqContext ctx) {
        return super.visitPrimaryStringEq(ctx);
    }

    @Override
    public String visitPrimarySubset(JmlParser.PrimarySubsetContext ctx) {
        return super.visitPrimarySubset(ctx);
    }

    @Override
    public String visitPrimarySuffixAccess(JmlParser.PrimarySuffixAccessContext ctx) {
        return "."
            + oneOf(ctx.IDENT(), ctx.TRANSIENT(), ctx.THIS(), ctx.INV(), ctx.INV_FREE(), ctx.MULT())
            + (ctx.LPAREN() != null ? "(" + accept(ctx.expressionlist()) + ")" : "");
    }

    @Override
    public String visitPrimarySuffixArray(JmlParser.PrimarySuffixArrayContext ctx) {
        return super.visitPrimarySuffixArray(ctx);
    }

    @Override
    public String visitPrimarySuffixCall(JmlParser.PrimarySuffixCallContext ctx) {
        return "(" + accept(ctx.expressionlist()) + ")";
    }

    @Override
    public String visitPrimaryTypeOf(JmlParser.PrimaryTypeOfContext ctx) {
        return super.visitPrimaryTypeOf(ctx);
    }

    @Override
    public String visitPrimaryUnion(JmlParser.PrimaryUnionContext ctx) {
        return super.visitPrimaryUnion(ctx);
    }

    @Override
    public String visitPrimaryUnionInf(JmlParser.PrimaryUnionInfContext ctx) {
        return super.visitPrimaryUnionInf(ctx);
    }

    @Override
    public String visitPrimaryValues(JmlParser.PrimaryValuesContext ctx) {
        return super.visitPrimaryValues(ctx);
    }

    @Override
    public String visitPrimaryWorksingSpace(JmlParser.PrimaryWorksingSpaceContext ctx) {
        return super.visitPrimaryWorksingSpace(ctx);
    }

    @Override
    public String visitPrimayTypeSpec(JmlParser.PrimayTypeSpecContext ctx) {
        return super.visitPrimayTypeSpec(ctx);
    }

    @Override
    public String visitQuantifiedvardecls(JmlParser.QuantifiedvardeclsContext ctx) {
        return accept(ctx.typespec()) + " " + accept(ctx.quantifiedvariabledeclarator(), ", ");

    }

    @Override
    public String visitQuantifiedvariabledeclarator(
            JmlParser.QuantifiedvariabledeclaratorContext ctx) {
        return accept(ctx.IDENT()) + accept(ctx.dims());
    }

    @Override
    public String visitQuantifier(JmlParser.QuantifierContext ctx) {
        return ctx.start.getText();
    }

    @Override
    public String visitReadable_if_clause(JmlParser.Readable_if_clauseContext ctx) {
        return super.visitReadable_if_clause(ctx);
    }

    @Override
    public String visitReferencetype(JmlParser.ReferencetypeContext ctx) {
        return accept(ctx.name());
    }

    @Override
    public String visitRelational_chain(JmlParser.Relational_chainContext ctx) {
        return accept(ctx.shiftexpr(), ctx.op);
    }

    @Override
    public String visitRelational_lockset(JmlParser.Relational_locksetContext ctx) {
        return accept(ctx.shiftexpr()) + " <# " + accept(ctx.postfixexpr());
    }

    @Override
    public String visitRelationalexpr(JmlParser.RelationalexprContext ctx) {
        return accept(ctx.children.getFirst());
    }

    @Override
    public String visitRepresents_clause(JmlParser.Represents_clauseContext ctx) {
        return "represents " + accept(ctx.lhs)
            + "="
            + accept(ctx.rhs)
            + accept(ctx.storeRefUnion())
            + accept("\\such_that", ctx.predicate())
            + ";";
    }

    @Override
    public String visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        return "requires " + accept(ctx.targetHeap())
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        return super.visitReturns_clause(ctx);
    }

    @Override
    public String visitSafe_math_expression(JmlParser.Safe_math_expressionContext ctx) {
        return "\\safe_math("
            + accept(ctx.expression())
            + ")";
    }

    @Override
    public String visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
        return "separates " + accept(ctx.sep)
            + accept("\n    \\declassifies", ctx.decl, ", ")
            + accept("\n    \\erases", ctx.decl, ", ")
            + accept("\n    \\new_objects", ctx.decl, ", ")
            + ";";
    }

    private String accept(String prefix, List<? extends ParseTree> ctxs, String delimiter) {
        if (ctxs.isEmpty()) {
            return "";
        }
        return prefix + accept(ctxs, delimiter);
    }

    @Override
    public String visitSeqdefterm(JmlParser.SeqdeftermContext ctx) {
        return "(\\seqdef "
            + accept(ctx.quantifiedvardecls()) + "; "
            + accept(ctx.expression(), "; ")
            + ")";
    }

    @Override
    public String visitSequenceCreate(JmlParser.SequenceCreateContext ctx) {
        return super.visitSequenceCreate(ctx);
    }

    @Override
    public String visitSequenceEmpty(JmlParser.SequenceEmptyContext ctx) {
        return super.visitSequenceEmpty(ctx);
    }

    @Override
    public String visitSequenceFuncs(JmlParser.SequenceFuncsContext ctx) {
        return super.visitSequenceFuncs(ctx);
    }

    @Override
    public String visitSequenceIgnore1(JmlParser.SequenceIgnore1Context ctx) {
        return super.visitSequenceIgnore1(ctx);
    }

    @Override
    public String visitSequenceReplace(JmlParser.SequenceReplaceContext ctx) {
        return super.visitSequenceReplace(ctx);
    }

    @Override
    public String visitSequenceReverse(JmlParser.SequenceReverseContext ctx) {
        return super.visitSequenceReverse(ctx);
    }

    @Override
    public String visitSequenceSub(JmlParser.SequenceSubContext ctx) {
        return super.visitSequenceSub(ctx);
    }

    @Override
    public String visitSet_statement(JmlParser.Set_statementContext ctx) {
        return super.visitSet_statement(ctx);
    }

    @Override
    public String visitShiftexpr(JmlParser.ShiftexprContext ctx) {
        return accept(ctx.additiveexpr(), ctx.op);
    }

    private String accept(List<? extends ParserRuleContext> expr, List<Token> op) {
        StringBuilder s = new StringBuilder(accept(expr.getFirst()));
        for (var i = 1; i < expr.size(); i++) {
            s.append(" ").append(op.get(i - 1)).append(" ").append(accept(expr.get(i)));
        }
        return s.toString();
    }

    @Override
    public String visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
        return super.visitSignals_clause(ctx);
    }

    @Override
    public String visitChildren(RuleNode node) {
        System.err.println(node.getClass().getSimpleName() + " not implemented " + node.getText());
        return super.visitChildren(node);
    }

    @Override
    protected String aggregateResult(String aggregate, String nextResult) {
        return ((aggregate != null) ? aggregate : "") +
                ((nextResult != null) ? nextResult : "");
    }

    @Override
    public String visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        return accept(ctx.SIGNALS_ONLY()) + " "
            + accept(ctx.referencetype(), ", ")
            + ";";
    }

    @Override
    public String visitSpec_body(JmlParser.Spec_bodyContext ctx) {
        return super.visitSpec_body(ctx);
    }

    @Override
    public String visitSpec_case(JmlParser.Spec_caseContext ctx) {
        return super.visitSpec_case(ctx);
    }

    @Override
    public String visitSpecquantifiedexpression(JmlParser.SpecquantifiedexpressionContext ctx) {
        return "(" +
            accept(ctx.quantifier()) + " "
            + accept(ctx.boundvarmodifiers())
            + accept(ctx.quantifiedvardecls()) + "; "
            + accept(ctx.expression(), "; ")
            + ")";

    }

    @Override
    public String visitSt_expr(JmlParser.St_exprContext ctx) {
        return accept(ctx.shiftexpr(0))
            + " <: "
            + accept(ctx.shiftexpr(1));
    }

    @Override
    public String visitStoreref(JmlParser.StorerefContext ctx) {
        return oneOf(ctx.NOTHING(), ctx.EVERYTHING(), ctx.NOT_SPECIFIED(), ctx.STRICTLY_NOTHING(),
            ctx.storeRefExpr());
    }

    @Override
    public String visitStoreRefExpr(JmlParser.StoreRefExprContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public String visitStoreRefIntersect(JmlParser.StoreRefIntersectContext ctx) {
        return accept(ctx.storeRefList());
    }

    @Override
    public String visitStoreRefList(JmlParser.StoreRefListContext ctx) {
        return accept(ctx.storeref(), ", ");
    }

    @Override
    public String visitStoreRefUnion(JmlParser.StoreRefUnionContext ctx) {
        return accept(ctx.list);
    }

    @Override
    public String visitStringliteral(JmlParser.StringliteralContext ctx) {
        return ctx.getText();
    }

    @Override
    public String visitTargetHeap(JmlParser.TargetHeapContext ctx) {
        return ctx.SPECIAL_IDENT().stream().map(it -> "<%s>".formatted(it.getSymbol().getText()))
                .collect(Collectors.joining());
    }

    @Override
    public String visitTermexpression(JmlParser.TermexpressionContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public String visitThis_(JmlParser.This_Context ctx) {
        return "this";
    }

    @Override
    public String visitTransactionUpdated(JmlParser.TransactionUpdatedContext ctx) {
        return ctx.getText();
    }

    @Override
    public String visitTrue_(JmlParser.True_Context ctx) {
        return "true";
    }

    @Override
    public String visitType(JmlParser.TypeContext ctx) {
        return accept(ctx.TYPE()) + oneOf(ctx.builtintype(), ctx.referencetype());
    }

    @Override
    public String visitTypespec(JmlParser.TypespecContext ctx) {
        return accept(ctx.type()) + accept(ctx.dims());
    }

    @Override
    public String visitUnaryexpr(JmlParser.UnaryexprContext ctx) {
        if (ctx.PLUS() != null)
            return "+" + accept(ctx.unaryexpr());
        if (ctx.MINUS() != null)
            return "-" + accept(ctx.unaryexpr());
        if (ctx.DECLITERAL() != null)
            return "-" + accept((ctx.DECLITERAL()));
        return accept(ctx.castexpr()) + accept(ctx.unaryexprnotplusminus());
    }

    @Override
    public String visitUnaryexprnotplusminus(JmlParser.UnaryexprnotplusminusContext ctx) {
        if (ctx.NOT() != null)
            return "!" + accept(ctx.unaryexpr());
        if (ctx.BITWISENOT() != null)
            return "~" + accept(ctx.unaryexpr());
        return accept(ctx.postfixexpr());

    }

    @Override
    public String visitVariant_function(JmlParser.Variant_functionContext ctx) {
        return "decreases " + accept(ctx.expression(), ", ");
    }

    @Override
    public String visitWhen_clause(JmlParser.When_clauseContext ctx) {
        return "when "
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitWorking_space_clause(JmlParser.Working_space_clauseContext ctx) {
        return "working_space "
            + accept(ctx.predornot())
            + ";";
    }

    @Override
    public String visitWritable_if_clause(JmlParser.Writable_if_clauseContext ctx) {
        return "writeable_if "
            + accept(ctx.expression())
            + ";";
    }
}
