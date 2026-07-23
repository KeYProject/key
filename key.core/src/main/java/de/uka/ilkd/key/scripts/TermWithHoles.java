/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.nparser.JavaKeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.scripts.meta.*;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@NullMarked
public class TermWithHoles {

    private final JTerm term;

    public TermWithHoles(JTerm term) {
        this.term = Objects.requireNonNull(term);
    }

    public static final Name HOLE_NAME = new Name("?");
    public static final Name HOLE_PREDICATE_NAME = new Name("?fml");
    public static final Name HOLE_SORT_DEP_NAME = new Name("?");
    public static final Name FOCUS_NAME = new Name("?focus");
    public static final Name ELLIPSIS_NAME = new Name("?find");

    private static final Logger LOGGER = LoggerFactory.getLogger(TermWithHoles.class);

    public boolean matches(PosInOccurrence posInOccurrence) {
        return getMatcher().matches(posInOccurrence);
    }

    public boolean matchesToplevel(SequentFormula sf) {
        return getMatcher().matchesToplevel(sf);
    }

    public TermComparisonWithHoles getMatcher() {
        return new TermComparisonWithHoles(term);
    }

    private static class NothingSort extends AbstractSort {
        private final Services services;

        public NothingSort(Services services) {
            super(new Name("Nothing"), true);
            this.services = services;
        }

        @Override
        public ImmutableSet<Sort> extendsSorts() {
            return ImmutableSet.from(services.getNamespaces().sorts().allElements()).remove(this);
        }

        @Override
        public boolean extendsTrans(Sort s) {
            return true;
        }

        @Override
        public boolean containsGenericSort() {
            return false;
        }
    }

    public static TermWithHoles fromString(EngineState engineState, String str) {
        JavaKeYParser p = ParsingFacade.createParser(CharStreams.fromString(str));
        p.allowMatchId = true;
        JavaKeYParser.TermContext term = p.termEOF().term();
        p.getErrorReporter().throwException();
        return fromParserContext(engineState, term);
    }

    public static TermWithHoles fromProofScriptExpression(EngineState engineState,
            JavaKeYParser.ProofScriptExpressionContext ctx) throws ConversionException {
        if (ctx.string_literal() != null) {
            String text = StringUtil.stripQuotes(ctx.string_literal().getText());
            return fromString(engineState, text);
        } else if (ctx.proofScriptCodeBlock() != null) {
            throw new ConversionException("A block cannot be used as a term");
        } else if (ctx.seq() != null) {
            throw new ConversionException("A sequent cannot be used as a term");
        } else {
            return fromParserContext(engineState, ctx.getRuleContext(ParserRuleContext.class, 0));
        }
    }

    public static TermWithHoles fromParserContext(EngineState state, ParseTree ctx) {
        var expressionBuilder =
            new ExpressionBuilder(state.getProof().getServices(), enrichState(state));
        expressionBuilder.setAbbrevMap(state.getAbbreviations());
        JTerm t = (JTerm) ctx.accept(expressionBuilder);
        List<BuildingIssue> warnings = expressionBuilder.getBuildingIssues();
        warnings.forEach(it -> LOGGER.warn("{}", it));
        warnings.clear();
        return new TermWithHoles(t);
    }

    private static NamespaceSet enrichState(EngineState state) {
        final var services = state.getProof().getServices();
        NamespaceSet ns = services.getNamespaces().copy();

        // Sort Nothing as bottom sort
        NothingSort nothing = new NothingSort(services);
        ns.sorts().add(nothing);

        ns.functions().addSafely(new JFunction(HOLE_NAME, nothing));
        ns.functions().addSafely(new JFunction(HOLE_PREDICATE_NAME, JavaDLTheory.FORMULA));
        ns.functions().addSafely(new JFunction(FOCUS_NAME, nothing, JavaDLTheory.ANY));
        ns.functions().addSafely(new JFunction(ELLIPSIS_NAME, nothing, JavaDLTheory.ANY));
        GenericSort g = new GenericSort(new Name("G"));
        GenericParameter p = new GenericParameter(g, GenericParameter.Variance.INVARIANT);
        final var decl = new ParametricFunctionDecl(HOLE_SORT_DEP_NAME,
            ImmutableList.singleton(p),
            new ImmutableArray<>(),
            g, null, false, false, false);
        ns.parametricFunctions().addSafely(decl);
        return ns;
    }

}
