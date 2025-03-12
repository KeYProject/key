/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.key_project.util.java.StringUtil.trim;

/**
 * @author Alexander Weigl
 * @version 1 (18.01.25)
 */
class ExprEvaluator extends KeYParserBaseVisitor<Object> {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprEvaluator.class);
    private final EngineState state;

    ExprEvaluator(EngineState engineState) {
        this.state = engineState;
    }

    @Override
    public Object visitBoolean_literal(KeYParser.Boolean_literalContext ctx) {
        return Boolean.parseBoolean(ctx.getText());
    }

    @Override
    public Object visitChar_literal(KeYParser.Char_literalContext ctx) {
        return ctx.getText().charAt(1); // skip "'"
    }

    @Override
    public Object visitInteger(KeYParser.IntegerContext ctx) {
        return Integer.parseInt(ctx.getText());
    }

    @Override
    public Object visitFloatLiteral(KeYParser.FloatLiteralContext ctx) {
        return Float.parseFloat(ctx.getText());
    }

    @Override
    public Object visitDoubleLiteral(KeYParser.DoubleLiteralContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitString_literal(KeYParser.String_literalContext ctx) {
        return trim(ctx.getText(), '"');
    }

    @Override
    public Object visitSeq(KeYParser.SeqContext ctx) {
        var expressionBuilder =
            new ExpressionBuilder(state.getProof().getServices(), state.getCurrentNamespaces());
        expressionBuilder.setAbbrevMap(state.getAbbreviations());
        var t = (Sequent) ctx.accept(expressionBuilder);
        var warnings = expressionBuilder.getBuildingIssues();
        warnings.forEach(it -> LOGGER.warn("{}", it));
        warnings.clear();
        return t;

    }

    @Override
    public Object visitTerm(KeYParser.TermContext ctx) {
        var expressionBuilder =
            new ExpressionBuilder(state.getProof().getServices(), state.getCurrentNamespaces());
        expressionBuilder.setAbbrevMap(state.getAbbreviations());
        var t = (Term) ctx.accept(expressionBuilder);
        var warnings = expressionBuilder.getBuildingIssues();
        warnings.forEach(it -> LOGGER.warn("{}", it));
        warnings.clear();
        return t;
    }

    @Override
    protected Object aggregateResult(Object aggregate, Object nextResult) {
        return nextResult == null ? aggregate : nextResult;
    }
}
