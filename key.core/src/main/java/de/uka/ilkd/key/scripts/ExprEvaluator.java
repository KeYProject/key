/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.net.URI;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParser.*;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;

import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.scripts.meta.ConversionException;
import de.uka.ilkd.key.scripts.meta.Converter;
import de.uka.ilkd.key.scripts.meta.NoSpecifiedConverterException;
import de.uka.ilkd.key.scripts.meta.ValueInjector;
import de.uka.ilkd.key.util.ANTLRUtil;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;

import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.sequent.SequentKit;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.key_project.util.java.StringUtil.trim;

/// Evaluates expression inside of proof script to their appropriate type.
///
/// - [SeqContext]: [Sequent]
/// - [Boolean_literalContext]: [Boolean]
/// - [IntegerContext]: [Integer]
/// - [DoubleLiteralContext]: [Double]
/// - [String_literalContext]: [String]
///
/// @author Alexander Weigl
/// @version 1 (18.01.25)
/// @see de.uka.ilkd.key.nparser.KeYParser.ProofScriptExpressionContext
class ExprEvaluator {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprEvaluator.class);
    private final EngineState state;

    ExprEvaluator(EngineState engineState) {
        this.state = engineState;
    }

    private Object evaluateExpression(ParserRuleContext ctx) {
        var expressionBuilder =
                new ExpressionBuilder(state.getProof().getServices(), state.getCurrentNamespaces());
        expressionBuilder.setAbbrevMap(state.getAbbreviations());
        var t = ctx.accept(expressionBuilder);
        var warnings = expressionBuilder.getBuildingIssues();
        warnings.forEach(it -> LOGGER.warn("{}", it));
        warnings.clear();
        return t;
    }

    public void addConvertersToValueInjector(ValueInjector v) {
        v.addConverter(String.class, ProofScriptExpressionContext.class, this::convertToString);
        v.addConverter(Boolean.class, ProofScriptExpressionContext.class, this::convertToBoolean);
        v.addConverter(boolean.class, ProofScriptExpressionContext.class, this::convertToBoolean);
        v.addConverter(Integer.class, ProofScriptExpressionContext.class, this::convertToInteger);
        v.addConverter(int.class, ProofScriptExpressionContext.class, this::convertToInteger);
        v.addConverter(JTerm.class, ProofScriptExpressionContext.class, this::convertToTerm);
        v.addConverter(Sequent.class, ProofScriptExpressionContext.class, this::convertToSequent);
        v.addConverter(TermWithHoles.class, ProofScriptExpressionContext.class,
                ctx -> TermWithHoles.fromProofScriptExpression(state, ctx));
        v.addConverter(SequentWithHoles.class, ProofScriptExpressionContext.class,
                ctx -> SequentWithHoles.fromParserContext(state, ctx));
        v.addConverter(ScriptBlock.class, ProofScriptExpressionContext.class, this::convertToScriptBlock);

    }

    private ScriptBlock convertToScriptBlock(ProofScriptExpressionContext ctx) throws ConversionException {
        if(ctx.proofScriptCodeBlock() == null) {
            throw new ConversionException("Need a script block here, not: " + ANTLRUtil.reconstructOriginal(ctx));
        }
        URI uri = KeyAst.ProofScript.getUri(ctx.start);
        return KeyAst.ProofScript.asAst(uri, ctx.proofScriptCodeBlock());
    }

    private JTerm convertToTerm(ProofScriptExpressionContext ctx) throws ConversionException {
        try {
            if (ctx.string_literal() != null) {
                String text = StringUtil.trim(ctx.string_literal().getText(), '"');
                return state.toTerm(text, null);
            } else if (ctx.proofScriptCodeBlock() != null) {
                throw new ConversionException("A block cannot be used as a term");
            } else {
                return (JTerm) evaluateExpression((ParserRuleContext) ctx.getChild(0));
            }
        } catch (Exception e) {
            throw new ConversionException("Cannot convert expression to term: " + ANTLRUtil.reconstructOriginal(ctx));
        }
    }

    private Sequent convertToSequent(ProofScriptExpressionContext ctx) throws ConversionException {
        try {
            if (ctx.string_literal() != null) {
                String text = StringUtil.trim(ctx.string_literal().getText(), '"');
                return state.toSequent(text);
            } else if (ctx.proofScriptCodeBlock() != null) {
                throw new ConversionException("A block cannot be used as a sequent");
            } else if (ctx.seq() != null) {
                return (Sequent) evaluateExpression(ctx.seq());
            } else {
                JTerm term = (JTerm) evaluateExpression((ParserRuleContext) ctx.getChild(0));
                return JavaDLSequentKit.createSuccSequent(ImmutableList.of(new SequentFormula(term)));
            }
        } catch (Exception e) {
            throw new ConversionException("Cannot convert expression to sequent: " + ANTLRUtil.reconstructOriginal(ctx));
        }
    }

    private Boolean convertToBoolean(ProofScriptExpressionContext ctx) throws ConversionException {
        if (ctx.boolean_literal() != null) {
            return Boolean.parseBoolean(ctx.boolean_literal().getText());
        } else if (ctx.string_literal() != null) {
            String text = StringUtil.trim(ctx.string_literal().getText(), '"');
            return Boolean.parseBoolean(text);
        } else {
            throw new ConversionException("Cannot convert expression to boolean: " + ANTLRUtil.reconstructOriginal(ctx));
        }
    }

    private Integer convertToInteger(ProofScriptExpressionContext proofScriptExpressionContext) throws ConversionException {
        if (proofScriptExpressionContext.integer() != null) {
            return Integer.parseInt(proofScriptExpressionContext.integer().getText());
        } else if (proofScriptExpressionContext.string_literal() != null) {
            String text = StringUtil.trim(proofScriptExpressionContext.string_literal().getText(), '"');
            return Integer.parseInt(text);
        } else {
            throw new ConversionException("Cannot convert expression to integer: " + ANTLRUtil.reconstructOriginal(proofScriptExpressionContext));
        }
    }

    private String convertToString(ProofScriptExpressionContext ctx) {
        if (ctx.string_literal() != null) {
            return StringUtil.trim(ctx.string_literal().getText(), '"');
        } else {
            return ANTLRUtil.reconstructOriginal(ctx).trim();
        }
    }

}