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
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.engine.ProverCore;
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

@NullMarked
public record TermWithHoles(JTerm term) {

    public static final Name HOLE_NAME = new Name("_");
    public static final Name HOLE_PREDICATE_NAME = new Name("__");
    public static final Name HOLE_SORT_DEP_NAME = new Name("___");

    private static final Logger LOGGER = LoggerFactory.getLogger(TermWithHoles.class);

    public boolean matches(JTerm other) {
        return TermComparisonWithHoles.compareModHoles(term, other);
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


    public static TermWithHoles fromParserContext(EngineState state, KeYParser.ProofScriptExpressionContext ctx) throws ScriptException {
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
        GenericSort g = new GenericSort(new Name("G"));
        ns.functions().addSafely(SortDependingFunction.createFirstInstance(g, HOLE_SORT_DEP_NAME, g,
                        new Sort[0], false));
        return ns;
    }

}
