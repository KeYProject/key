/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml.translation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.speclang.jml.JmlSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassAxiom;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassInv;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLDepends;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLInitially;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLRepresents;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.jml.body.JmlBodyClauseKind;
import com.github.javaparser.ast.jml.body.JmlClassAccessibleDeclaration;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.ContractType;
import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlInfFlowClause;
import com.github.javaparser.ast.jml.clauses.JmlLabeledClause;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause;
import com.github.javaparser.ast.jml.clauses.JmlSignalsOnlyClause;
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause;
import org.antlr.v4.runtime.ParserRuleContext;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.DECREASES;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.DIVERGES;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.INFORMATION_FLOW;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.MEASURED_BY;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.RETURNS;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS_ONLY;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ACCESSIBLE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ASSIGNABLE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ENSURES;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ENSURES_FREE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.REQUIRES;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.REQUIRES_FREE;

/**
 * Converts a {@link JmlSpec} (a JMLtk AST node) into KeY's textual JML representation
 * ({@link TextualJMLConstruct}), which the rest of the KeY translation pipeline consumes.
 * <p>
 * This is necessary because the KeY specific translation consumes parse trees of KeY's own JML
 * grammar ({@code JmlParser.g4}). The individual constructs are therefore re-serialized to text
 * and re-parsed with the respective grammar rule. Due to differences between the JMLtk printer
 * and KeY's grammar, the text is assembled per construct kind rather than taken from
 * {@code Node#toString()} blindly.
 */
public final class JmlToTextual {
    private static final Logger LOGGER = LoggerFactory.getLogger(JmlToTextual.class);

    private static final Map<Modifier.DefaultKeyword, JMLModifier> JML_MODIFIERS;

    static {
        Map<Modifier.DefaultKeyword, JMLModifier> m = new HashMap<>();
        for (JMLModifier jm : JMLModifier.values()) {
            m.put(jm.getParserKeyword(), jm);
        }
        JML_MODIFIERS = m;
    }

    private JmlToTextual() {
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Converts the given contract into textual spec cases. The main contract and all
     * sub-contracts (nested specification blocks) are returned. Loop contracts are marked
     * accordingly.
     *
     * @return one spec case per (sub-)contract
     */
    public static ImmutableList<TextualJMLSpecCase> toSpecCases(JmlSpec spec) {
        if (!(spec.node() instanceof JmlContract contract)) {
            throw new IllegalArgumentException(
                "Expected a JmlContract but got " + spec.node().getClass().getSimpleName());
        }
        return toSpecCases(contract);
    }

    /**
     * Converts the given contract into textual spec cases, main contract plus sub-contracts.
     */
    public static ImmutableList<TextualJMLSpecCase> toSpecCases(JmlContract contract) {
        ImmutableList<TextualJMLSpecCase> result = ImmutableList.of();
        result = result.append(toSpecCase(contract));
        for (JmlContract sub : contract.getSubContracts()) {
            result = result.append(toSpecCase(sub));
        }
        return result;
    }

    /**
     * Converts a loop invariant contract (jmltk {@link ContractType#LOOP_INV}) into a textual
     * loop specification.
     */
    public static TextualJMLLoopSpec toLoopSpec(JmlSpec spec) {
        if (!(spec.node() instanceof JmlContract contract)) {
            throw new IllegalArgumentException(
                "Expected a JmlContract but got " + spec.node().getClass().getSimpleName());
        }
        TextualJMLLoopSpec loopSpec = new TextualJMLLoopSpec(mapModifiers(contract.getModifiers()));
        for (JmlClause clause : contract.getClauses()) {
            try {
                handleLoopSpecClause(loopSpec, clause);
            } catch (RuntimeException e) {
                LOGGER.warn("Skipping unsupported loop specification clause: {}", e.getMessage());
            }
        }
        return loopSpec;
    }

    public static TextualJMLClassInv toClassInv(JmlSpec spec) {
        JmlClassExprDeclaration decl =
            classExpr(spec, JmlBodyClauseKind.INVARIANT, JmlBodyClauseKind.INVARIANT_FREE);
        boolean free = decl.getKind() == JmlBodyClauseKind.INVARIANT_FREE;
        var ctx = parse(JmlParser::class_invariant,
            (free ? "invariant_free " : "invariant ") + decl.getInvariant() + ";");
        return new TextualJMLClassInv(mapModifiers(decl.getModifiers()), ctx, free);
    }

    public static TextualJMLInitially toInitially(JmlSpec spec) {
        JmlClassExprDeclaration decl = classExpr(spec, JmlBodyClauseKind.INITIALLY);
        var ctx = parse(JmlParser::initially_clause, "initially " + decl.getInvariant() + ";");
        return new TextualJMLInitially(mapModifiers(decl.getModifiers()),
            new LabeledParserRuleContext(ctx));
    }

    public static TextualJMLClassAxiom toClassAxiom(JmlSpec spec) {
        JmlClassExprDeclaration decl = classExpr(spec, JmlBodyClauseKind.AXIOM,
            JmlBodyClauseKind.CONSTRAINT, JmlBodyClauseKind.CONSTRAINT_REDUNDANTLY);
        if (decl.getKind() != JmlBodyClauseKind.AXIOM) {
            LOGGER.warn("Skipping unsupported class level construct: {}", decl.getKind());
            return null;
        }
        var ctx = parse(JmlParser::class_axiom, "axiom " + decl.getInvariant() + ";");
        return new TextualJMLClassAxiom(mapModifiers(decl.getModifiers()),
            new LabeledParserRuleContext(ctx));
    }

    public static TextualJMLRepresents toRepresents(JmlSpec spec) {
        if (!(spec.node() instanceof JmlRepresentsDeclaration decl)) {
            throw new IllegalArgumentException("Expected a JmlRepresentsDeclaration but got "
                + spec.node().getClass().getSimpleName());
        }
        var ctx = parse(JmlParser::represents_clause,
            "represents " + decl.getName() + " = " + decl.getExpr() + ";");
        return new TextualJMLRepresents(mapModifiers(decl.getModifiers()),
            new LabeledParserRuleContext(ctx));
    }

    public static TextualJMLDepends toDepends(JmlSpec spec) {
        if (!(spec.node() instanceof JmlClassAccessibleDeclaration decl)) {
            throw new IllegalArgumentException("Expected a JmlClassAccessibleDeclaration but got "
                + spec.node().getClass().getSimpleName());
        }
        StringBuilder text = new StringBuilder("accessible ");
        text.append(decl.getVariable()).append(": ");
        text.append(exprList(decl.getExpressions()));
        if (decl.getMeasuredBy().isPresent()) {
            text.append(" \\measured_by ").append(decl.getMeasuredBy().get());
        }
        text.append(';');
        var ctx = parse(JmlParser::accessible_clause, text.toString());
        return new TextualJMLDepends(mapModifiers(decl.getModifiers()),
            new Name[] { HeapLDT.BASE_HEAP_NAME }, new LabeledParserRuleContext(ctx));
    }

    /**
     * Re-serializes a model method declaration into KeY's textual form.
     */
    public static TextualJMLMethodDecl toMethodDecl(JmlSpec spec) {
        if (!(spec.node() instanceof JmlMethodDeclaration decl)) {
            throw new IllegalArgumentException(
                "Expected a JmlMethodDeclaration but got "
                    + spec.node().getClass().getSimpleName());
        }
        MethodDeclaration m = decl.getMethodDeclaration();
        StringBuilder text = new StringBuilder();
        text.append(m.getType()).append(' ').append(m.getName()).append('(');
        text.append(m.getParameters().stream()
                .map(p -> p.getType() + " " + p.getName()).collect(java.util.stream.Collectors
                        .joining(", ")));
        text.append(')');
        if (m.getBody().isPresent()) {
            text.append(' ').append(m.getBody().get());
        } else {
            text.append(';');
        }
        var ctx = parse(JmlParser::method_declaration, text.toString());
        return new TextualJMLMethodDecl(mapModifiers(m.getModifiers()), ctx);
    }

    /**
     * Maps JMLtk modifiers onto KeY's {@link JMLModifier}s. JML documentation modifiers (which
     * are handled by JMLtk) are filtered out.
     */
    public static ImmutableList<JMLModifier> mapModifiers(NodeList<Modifier> modifiers) {
        ImmutableList<JMLModifier> result = ImmutableList.nil();
        for (Modifier mod : modifiers) {
            if (!(mod.getKeyword() instanceof Modifier.DefaultKeyword kw)) {
                continue;
            }
            JMLModifier jm = JML_MODIFIERS.get(kw);
            if (jm != null) {
                result = result.append(jm);
            }
        }
        return result;
    }

    /**
     * Maps a JMLtk behavior onto KeY's {@link Behavior}.
     */
    public static Behavior mapBehavior(com.github.javaparser.ast.stmt.Behavior behavior) {
        return switch (behavior) {
            case NONE -> Behavior.NONE;
            case BEHAVIOR -> Behavior.BEHAVIOR;
            case NORMAL -> Behavior.NORMAL_BEHAVIOR;
            case EXCEPTIONAL -> Behavior.EXCEPTIONAL_BEHAVIOR;
            case MODEL -> Behavior.MODEL_BEHAVIOR;
            case BREAK -> Behavior.BREAK_BEHAVIOR;
            case CONTINUE -> Behavior.CONTINUE_BEHAVIOR;
            case RETURN -> Behavior.RETURN_BEHAVIOR;
            // `abrupt` is a generic behavior encompassing break/continue/return
            case ABRUPT -> Behavior.NONE;
        };
    }

    // -------------------------------------------------------------------------
    // contract (spec case) handling
    // -------------------------------------------------------------------------

    private static TextualJMLSpecCase toSpecCase(JmlContract contract) {
        TextualJMLSpecCase specCase = new TextualJMLSpecCase(mapModifiers(contract.getModifiers()),
            mapBehavior(contract.getBehavior()));
        contract.getName().ifPresent(n -> specCase.addName(n.getIdentifier()));
        if (contract.getType() == ContractType.LOOP) {
            specCase.setLoopContract(true);
        }
        boolean loop = contract.getType() == ContractType.LOOP;
        for (JmlClause clause : contract.getClauses()) {
            try {
                handleContractClause(specCase, clause, loop);
            } catch (RuntimeException e) {
                LOGGER.warn("Skipping unsupported contract clause: {}", e.getMessage());
            }
        }
        return specCase;
    }

    private static void handleContractClause(TextualJMLSpecCase specCase, JmlClause clause,
            boolean loopContract) {
        if (clause instanceof JmlSimpleExprClause simple) {
            handleSimpleClause(specCase, simple, loopContract);
        } else if (clause instanceof JmlMultiExprClause multi) {
            handleMultiClause(specCase, multi, loopContract);
        } else if (clause instanceof JmlLabeledClause labeled) {
            handleLabeledClause(specCase, labeled);
        } else if (clause instanceof JmlSignalsClause signals) {
            handleSignalsClause(specCase, signals);
        } else if (clause instanceof JmlSignalsOnlyClause signalsOnly) {
            handleSignalsOnlyClause(specCase, signalsOnly);
        } else if (clause instanceof JmlInfFlowClause infFlow) {
            handleInfFlowClause(specCase, infFlow, loopContract);
        } else {
            throw new IllegalArgumentException(
                "Unsupported contract clause: " + clause.getClass().getSimpleName() + " " + clause);
        }
    }

    private static void handleSimpleClause(TextualJMLSpecCase specCase, JmlSimpleExprClause clause,
            boolean loopContract) {
        String expr = clause.getExpression().toString();
        switch (clause.getKind()) {
            case REQUIRES, REQUIRES_FREE -> {
                boolean free = clause.getKind() == JmlClauseKind.REQUIRES_FREE;
                List<String> heaps = heaps(clause.getHeaps());
                var ctx = parse(JmlParser::requires_clause,
                    (free ? "requires_free" : "requires") + heapsText(heaps) + " " + expr + ";");
                addHeapClause(specCase, free ? REQUIRES_FREE : REQUIRES, heaps, ctx,
                    free ? OriginTermLabel.SpecType.REQUIRES_FREE
                            : OriginTermLabel.SpecType.REQUIRES);
            }
            case ENSURES, ENSURES_FREE -> {
                boolean free = clause.getKind() == JmlClauseKind.ENSURES_FREE;
                List<String> heaps = heaps(clause.getHeaps());
                var ctx = parse(JmlParser::ensures_clause,
                    (free ? "ensures_free" : "ensures") + heapsText(heaps) + " " + expr + ";");
                addHeapClause(specCase, free ? ENSURES_FREE : ENSURES, heaps, ctx,
                    free ? OriginTermLabel.SpecType.ENSURES_FREE
                            : OriginTermLabel.SpecType.ENSURES);
            }
            case DECREASES, DECREASING -> {
                var ctx = parse(JmlParser::variant_function, "decreasing " + expr + ";");
                specCase.addClause(DECREASES, LabeledParserRuleContext
                        .createLabeledParserRuleContext(ctx, OriginTermLabel.SpecType.DECREASES,
                            true));
            }
            case RETURNS, RETURNS_REDUNDANTLY -> {
                var ctx = parse(JmlParser::returns_clause, "returns " + expr + ";");
                specCase.addClause(RETURNS, LabeledParserRuleContext
                        .createLabeledParserRuleContext(ctx, OriginTermLabel.SpecType.RETURNS,
                            true));
            }
            case LOOP_INVARIANT, LOOP_INVARIANT_FREE, LOOP_INVARIANT_REDUNDANTLY, MAINTAINING,
                    MAINTAINING_REDUNDANTLY, INVARIANT, INVARIANT_REDUNDANTLY -> {
                // loop invariants are handled by toLoopSpec; within a loop contract they
                // are not expressible in KeY's grammar
                throw new IllegalArgumentException(
                    "Loop invariant clause inside a loop/block/method contract: " + clause);
            }
            default -> throw new IllegalArgumentException(
                "Unsupported clause kind: " + clause.getKind() + " " + clause);
        }
    }

    private static void handleMultiClause(TextualJMLSpecCase specCase, JmlMultiExprClause clause,
            boolean loopContract) {
        String exprs = exprList(clause.getExpressions());
        switch (clause.getKind()) {
            case ASSIGNABLE, ASSIGNABLE_REDUNDANTLY, MODIFIABLE, MODIFIABLE_REDUNDANTLY, MODIFIES,
                    MODIFIES_REDUNDANTLY -> {
                List<String> heaps = heaps(clause.getHeaps());
                var ctx = parse(JmlParser::assignable_clause,
                    "assignable" + heapsText(heaps) + " " + exprs + ";");
                addHeapClause(specCase, ASSIGNABLE, heaps, ctx,
                    OriginTermLabel.SpecType.ASSIGNABLE);
            }
            case ACCESSIBLE, CALLABLE, CALLABLE_REDUNDANTLY -> {
                List<String> heaps = heaps(clause.getHeaps());
                var ctx = parse(JmlParser::accessible_clause,
                    "accessible" + heapsText(heaps) + " " + exprs + ";");
                addHeapClause(specCase, ACCESSIBLE, heaps, ctx,
                    OriginTermLabel.SpecType.ACCESSIBLE);
            }
            case MEASURED_BY -> {
                var ctx = parse(JmlParser::measured_by_clause, "measured_by " + exprs + ";");
                specCase.addClause(MEASURED_BY, LabeledParserRuleContext
                        .createLabeledParserRuleContext(ctx, OriginTermLabel.SpecType.MEASURED_BY,
                            true));
            }
            case DIVERGES, DIVERGES_REDUNDANTLY -> {
                var ctx = parse(JmlParser::diverges_clause, "diverges " + exprs + ";");
                specCase.addClause(DIVERGES, new LabeledParserRuleContext(ctx));
            }
            default -> throw new IllegalArgumentException(
                "Unsupported clause kind: " + clause.getKind() + " " + clause);
        }
    }

    private static void handleLabeledClause(TextualJMLSpecCase specCase, JmlLabeledClause clause) {
        String label = clause.getLabel().map(SimpleName::getIdentifier).orElse(" ");
        String expr = clause.getExpr() == null ? "" : " " + clause.getExpr();
        switch (clause.getKind()) {
            case BREAKS, BREAKS_REDUNDANTLY -> {
                var ctx = parse(JmlParser::breaks_clause,
                    "breaks (" + label.trim() + ")" + expr + ";");
                specCase.addClause(
                    de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.BREAKS,
                    LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                        OriginTermLabel.SpecType.BREAKS, true));
            }
            case CONTINUES, CONTINUES_REDUNDANTLY -> {
                var ctx = parse(JmlParser::continues_clause,
                    "continues (" + label.trim() + ")" + expr + ";");
                specCase.addClause(
                    de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.CONTINUES,
                    LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                        OriginTermLabel.SpecType.CONTINUES, true));
            }
            default -> throw new IllegalArgumentException(
                "Unsupported labeled clause kind: " + clause.getKind());
        }
    }

    private static void handleSignalsClause(TextualJMLSpecCase specCase, JmlSignalsClause clause) {
        var param = clause.getParameter();
        var ctx = parse(JmlParser::signals_clause,
            "signals (" + param.getType() + " " + param.getName() + ")" +
                (clause.getExpression() == null ? "" : " " + clause.getExpression()) + ";");
        specCase.addClause(SIGNALS, LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
            OriginTermLabel.SpecType.SIGNALS, true));
    }

    private static void handleSignalsOnlyClause(TextualJMLSpecCase specCase,
            JmlSignalsOnlyClause clause) {
        String types = clause.getTypes().stream().map(t -> t.asString())
                .collect(java.util.stream.Collectors.joining(", "));
        var ctx = parse(JmlParser::signals_only_clause, "signals_only " + types + ";");
        specCase.addClause(SIGNALS_ONLY, LabeledParserRuleContext
                .createLabeledParserRuleContext(ctx, OriginTermLabel.SpecType.SIGNALS_ONLY, true));
    }

    private static void handleInfFlowClause(TextualJMLSpecCase specCase, JmlInfFlowClause clause,
            boolean loopContract) {
        String determined = infFlowList(clause.getExpressions());
        switch (clause.getKind()) {
            case SEPARATES, LOOP_SEPARATES -> {
                String text = "separates " + determined + infFlowTail(clause);
                var ctx = parse(JmlParser::separates_clause, text);
                specCase.addClause(INFORMATION_FLOW, new LabeledParserRuleContext(ctx));
            }
            case DETERMINES -> {
                String text = "determines " + determined + " \\by " + infFlowBy(clause)
                    + infFlowTail(clause);
                var ctx = parse(JmlParser::determines_clause, text);
                specCase.addClause(INFORMATION_FLOW, new LabeledParserRuleContext(ctx));
            }
            default -> throw new IllegalArgumentException(
                "Unsupported information flow clause kind: " + clause.getKind());
        }
    }

    private static String infFlowBy(JmlInfFlowClause clause) {
        if (clause.getBy().isEmpty()) {
            return "\\itself";
        }
        return exprList(clause.getBy());
    }

    private static String infFlowTail(JmlInfFlowClause clause) {
        StringBuilder text = new StringBuilder();
        if (!clause.getDeclassifies().isEmpty()) {
            text.append(" \\declassifies ").append(exprList(clause.getDeclassifies()));
        }
        if (!clause.getErases().isEmpty()) {
            text.append(" \\erases ").append(exprList(clause.getErases()));
        }
        if (!clause.getNewObjects().isEmpty()) {
            text.append(" \\new_objects ").append(exprList(clause.getNewObjects()));
        }
        return text.toString();
    }

    private static String infFlowList(NodeList<Expression> expressions) {
        return expressions.isEmpty() ? "\\nothing" : exprList(expressions);
    }

    // -------------------------------------------------------------------------
    // loop specification (loop invariant contract) handling
    // -------------------------------------------------------------------------

    private static void handleLoopSpecClause(TextualJMLLoopSpec loopSpec, JmlClause clause) {
        if (clause instanceof JmlSimpleExprClause simple) {
            switch (simple.getKind()) {
                case LOOP_INVARIANT, LOOP_INVARIANT_REDUNDANTLY, MAINTAINING,
                        MAINTAINING_REDUNDANTLY, INVARIANT, INVARIANT_REDUNDANTLY -> {
                    boolean free = false;
                    List<String> heaps = heaps(simple.getHeaps());
                    var ctx = parse(JmlParser::loop_invariant,
                        "loop_invariant" + heapsText(heaps) + " " + simple.getExpression() + ";");
                    for (String heap : heaps) {
                        loopSpec.addClause(TextualJMLLoopSpec.ClauseHd.INVARIANT, new Name(heap),
                            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                                OriginTermLabel.SpecType.LOOP_INVARIANT, true));
                    }
                }
                case LOOP_INVARIANT_FREE -> {
                    List<String> heaps = heaps(simple.getHeaps());
                    var ctx = parse(JmlParser::loop_invariant,
                        "loop_invariant_free" + heapsText(heaps) + " " + simple.getExpression()
                            + ";");
                    for (String heap : heaps) {
                        loopSpec.addClause(TextualJMLLoopSpec.ClauseHd.INVARIANT_FREE,
                            new Name(heap), LabeledParserRuleContext.createLabeledParserRuleContext(
                                ctx, OriginTermLabel.SpecType.LOOP_INVARIANT_FREE, true));
                    }
                }
                case DECREASES, DECREASING, DECREASES_REDUNDANTLY -> {
                    var ctx = parse(JmlParser::variant_function,
                        "decreasing " + simple.getExpression() + ";");
                    loopSpec.setVariant(LabeledParserRuleContext
                            .createLabeledParserRuleContext(ctx, OriginTermLabel.SpecType.DECREASES,
                                true));
                }
                default -> throw new IllegalArgumentException(
                    "Unsupported loop specification clause kind: " + simple.getKind());
            }
        } else if (clause instanceof JmlMultiExprClause multi) {
            switch (multi.getKind()) {
                case ASSIGNABLE, ASSIGNABLE_REDUNDANTLY, MODIFIABLE, MODIFIABLE_REDUNDANTLY,
                        MODIFIES, MODIFIES_REDUNDANTLY -> {
                    List<String> heaps = heaps(multi.getHeaps());
                    String exprs = exprList(multi.getExpressions());
                    var ctx = parse(JmlParser::loop_assignable_clause,
                        "loop_assignable" + heapsText(heaps) + " " + exprs + ";");
                    for (String heap : heaps) {
                        loopSpec.addClause(TextualJMLLoopSpec.ClauseHd.ASSIGNABLE, new Name(heap),
                            LabeledParserRuleContext.createLabeledParserRuleContext(ctx,
                                OriginTermLabel.SpecType.ASSIGNABLE, true));
                    }
                }
                default -> throw new IllegalArgumentException(
                    "Unsupported loop specification clause kind: " + multi.getKind());
            }
        } else if (clause instanceof JmlInfFlowClause infFlow) {
            switch (infFlow.getKind()) {
                case DETERMINES -> {
                    String text = "determines " + infFlowList(infFlow.getExpressions()) + " \\by "
                        + infFlowBy(infFlow) + infFlowTail(infFlow);
                    var ctx = parse(JmlParser::determines_clause, text);
                    loopSpec.addClause(TextualJMLLoopSpec.ClauseHd.INFORMATION_FLOW,
                        HeapLDT.BASE_HEAP_NAME, new LabeledParserRuleContext(ctx));
                }
                case SEPARATES, LOOP_SEPARATES -> {
                    String text = "separates " + infFlowList(infFlow.getExpressions())
                        + infFlowTail(infFlow);
                    var ctx = parse(JmlParser::separates_clause, text);
                    loopSpec.addClause(TextualJMLLoopSpec.ClauseHd.INFORMATION_FLOW,
                        new LabeledParserRuleContext(ctx));
                }
                case LOOP_DETERMINES -> {
                    String text = "loop_determines " + infFlowList(infFlow.getExpressions())
                        + " \\by \\itself" + newObjectsTail(infFlow);
                    var ctx = parse(JmlParser::loop_determines_clause, text);
                    loopSpec.addClause(TextualJMLLoopSpec.ClauseHd.INFORMATION_FLOW,
                        HeapLDT.BASE_HEAP_NAME, new LabeledParserRuleContext(ctx));
                }
                default -> throw new IllegalArgumentException(
                    "Unsupported loop specification clause kind: " + infFlow.getKind());
            }
        } else {
            throw new IllegalArgumentException("Unsupported loop specification clause: "
                + clause.getClass().getSimpleName() + " " + clause);
        }
    }

    private static String newObjectsTail(JmlInfFlowClause clause) {
        if (clause.getNewObjects().isEmpty()) {
            return "";
        }
        return " \\new_objects " + exprList(clause.getNewObjects());
    }

    // -------------------------------------------------------------------------
    // helpers
    // -------------------------------------------------------------------------

    private interface RuleParser<R extends ParserRuleContext> {
        R parse(JmlParser parser);
    }

    /**
     * Parses the given text with the given requested rule of KeY's JML parser.
     */
    private static <R extends ParserRuleContext> R parse(RuleParser<R> rule, String text) {
        JmlParser parser = JmlFacade.createParser(JmlFacade.createLexer(text));
        R ctx = rule.parse(parser);
        parser.getErrorReporter().throwException();
        return ctx;
    }

    private static JmlClassExprDeclaration classExpr(JmlSpec spec, JmlBodyClauseKind... kinds) {
        if (!(spec.node() instanceof JmlClassExprDeclaration decl)) {
            throw new IllegalArgumentException("Expected a JmlClassExprDeclaration but got "
                + spec.node().getClass().getSimpleName());
        }
        for (JmlBodyClauseKind kind : kinds) {
            if (decl.getKind() == kind) {
                return decl;
            }
        }
        throw new IllegalArgumentException(
            "Unsupported class level construct kind: " + decl.getKind());
    }

    private static void addHeapClause(TextualJMLSpecCase specCase, TextualJMLSpecCase.ClauseHd kind,
            List<String> heaps, ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        for (String heap : heaps) {
            specCase.addClause(kind, new Name(heap),
                LabeledParserRuleContext.createLabeledParserRuleContext(ctx, specType, true));
        }
    }

    /**
     * Returns the heap names of the given (optional) list, fallback to the (single) base heap.
     */
    private static List<String> heaps(Optional<NodeList<SimpleName>> heaps) {
        return heaps.isPresent() ? heaps(heaps.get()) : baseHeaps();
    }

    private static List<String> heaps(NodeList<SimpleName> heaps) {
        if (heaps == null || heaps.isEmpty()) {
            return baseHeaps();
        }
        List<String> result = new ArrayList<>(heaps.size());
        for (SimpleName h : heaps) {
            result.add(h.getIdentifier());
        }
        return result;
    }

    private static List<String> baseHeaps() {
        return List.of(HeapLDT.BASE_HEAP_NAME.toString());
    }

    private static String heapsText(List<String> heaps) {
        StringBuilder sb = new StringBuilder();
        for (String heap : heaps) {
            sb.append('<').append(heap).append('>');
        }
        return sb.toString();
    }

    private static String exprList(List<Expression> expressions) {
        return expressions.stream().map(Expression::toString)
                .collect(java.util.stream.Collectors.joining(", "));
    }
}
