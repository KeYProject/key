/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.scripts.meta.*;
import de.uka.ilkd.key.strategy.FocussedBreakpointRuleApplicationManager;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static de.uka.ilkd.key.strategy.StrategyProperties.*;

/*

y < (x+0) + y + (x+0),
a -> y < (x+0) + y + (x+0)


rule plus_zero on: ?????

--->   a -> y < (x+0) + y + FOCUS(x+0)

--->  _ -> (... _ + (_+0) ...)

---> _ -> _find(_ + _focus(_ + 0))

---> ? -> ?find(? + ?focus(? + 0))

---> ?_ -> ?find(?_ + ?focus(_ + 0))
 */

@NullMarked
public class TermWithHoles {

    private final JTerm term;
    public TermWithHoles(JTerm term) {
        this.term = term;
    }


    public static final Name HOLE_NAME = new Name("?");
    public static final Name HOLE_PREDICATE_NAME = new Name("?fml");
    public static final Name HOLE_SORT_DEP_NAME = new Name("?");
    public static final Name FOCUS_NAME = new Name("?focus");

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
    }

    public static TermWithHoles fromString(EngineState engineState, String str) {
        KeyAst.Term term = ParsingFacade.parseExpression(CharStreams.fromString(str));
        return fromParserContext(engineState, term.ctx);
    }

    public static TermWithHoles fromParserContext(EngineState state, ParserRuleContext ctx) {
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
        NamespaceSet ns = state.getProof().getServices().getNamespaces().copy();

        // Sort Nothing as bottom sort
        NothingSort nothing = new NothingSort(state.getProof().getServices());
        ns.sorts().add(nothing);

        ns.functions().addSafely(new JFunction(HOLE_NAME, nothing));
        ns.functions().addSafely(new JFunction(HOLE_PREDICATE_NAME, JavaDLTheory.FORMULA));
        ns.functions().addSafely(new JFunction(FOCUS_NAME, nothing, JavaDLTheory.ANY));
        GenericSort g = new GenericSort(new Name("G"));
        ns.functions().addSafely(SortDependingFunction.createFirstInstance(g, HOLE_SORT_DEP_NAME, g,
                        new Sort[0], false));
        return ns;
    }

}
