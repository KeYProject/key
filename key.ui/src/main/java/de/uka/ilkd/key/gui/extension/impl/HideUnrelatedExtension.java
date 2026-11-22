/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.extension.impl;

import java.awt.event.ActionEvent;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import javax.swing.Action;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.RelatedFormulas;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Adds a context menu entry to the sequent view that hides all formulae of the selected goal that
 * are not transitively related to the clicked term by shared syntactic subterms.
 * <p>
 * The formulae are hidden by applying the existing {@code hide_left} / {@code hide_right} rules and
 * can be restored via the generated {@code insert_hidden} taclets ("Insert Hidden").
 */
@KeYGuiExtension.Info(name = "Hide Unrelated Formulas",
    description = "Hides all formulae that are not transitively related to the clicked term. "
        + "Hidden formulae can be restored via 'Insert Hidden'.",
    experimental = true, optional = true, priority = 100)
public class HideUnrelatedExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu {
    private static final Logger LOGGER = LoggerFactory.getLogger(HideUnrelatedExtension.class);

    private static final Name HIDE_LEFT = new Name("hide_left");
    private static final Name HIDE_RIGHT = new Name("hide_right");

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public <T> List<Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind,
                @Nullable T underlyingObject) {
            if (kind != ContextMenuKind.SEQUENT_VIEW) {
                return List.of();
            }
            if (!(underlyingObject instanceof PosInSequent pos)) {
                return List.of();
            }
            PosInOccurrence pio = pos.getPosInOccurrence();
            if (pio == null || pio.posInTerm() == null) {
                // no usable term position (e.g. a click on the sequent itself)
                return List.of();
            }
            if (mediator == null || mediator.getSelectedGoal() == null) {
                return List.of();
            }
            return List.of(new HideUnrelatedAction(mediator, mediator.getSelectedGoal(), pio));
        }
    };

    @Override
    public <T> List<Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind,
            T underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    /**
     * The action that hides all formulae of the selected goal that are not transitively related to
     * the clicked term.
     */
    private static class HideUnrelatedAction extends KeyAction {
        private final KeYMediator mediator;
        private final Goal goal;
        private final PosInOccurrence clicked;

        HideUnrelatedAction(KeYMediator mediator, Goal goal, PosInOccurrence clicked) {
            this.mediator = mediator;
            this.goal = goal;
            this.clicked = clicked;
            setName("Show only formulas related to this term");
            setTooltip("<html>Hides all formulae of the selected goal that are not transitively "
                + "related (by shared syntactic subterms) to the clicked term.<br>"
                + "The hidden formulae can be restored via 'Insert Hidden'.</html>");
            setEnabled(isApplicable());
        }

        /**
         * @return the formulae of the goal that are related to the clicked term, or empty if the
         *         clicked formula does not occur in the goal
         */
        private Optional<Set<SequentFormula>> plan() {
            return RelatedFormulas.computeKeptFormulas(goal.sequent(),
                (JTerm) clicked.subTerm(), clicked.sequentFormula());
        }

        private boolean isApplicable() {
            Optional<Set<SequentFormula>> plan = plan();
            return plan.isPresent()
                    && !RelatedFormulas.hidesNothing(goal.sequent(), plan.get())
                    && lookupHideTaclet(true) != null && lookupHideTaclet(false) != null;
        }

        private @Nullable FindTaclet lookupHideTaclet(boolean inAntec) {
            return (FindTaclet) goal.proof().getEnv().getInitConfigForEnvironment()
                    .lookupActiveTaclet(inAntec ? HIDE_LEFT : HIDE_RIGHT);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Optional<Set<SequentFormula>> plan = plan();
            if (plan.isEmpty()) {
                return;
            }
            Set<SequentFormula> kept = plan.get();

            Goal current = goal;
            for (SequentFormula sf : goal.sequent().antecedent()) {
                if (!kept.contains(sf)) {
                    current = applyHide(current, sf, true);
                }
            }
            for (SequentFormula sf : goal.sequent().succedent()) {
                if (!kept.contains(sf)) {
                    current = applyHide(current, sf, false);
                }
            }

            // refresh the sequent view if the selected node was the goal we modified
            if (mediator.getSelectedNode() == goal.node()) {
                mediator.getSelectionModel().setSelectedNode(current.node());
            }
        }

        /**
         * Applies {@code hide_left} or {@code hide_right} to the given formula on the current goal
         * and returns the resulting goal.
         */
        private Goal applyHide(Goal current, SequentFormula sf, boolean inAntec) {
            FindTaclet hideTaclet = lookupHideTaclet(inAntec);
            if (hideTaclet == null) {
                LOGGER.warn("Could not look up the {} rule; cannot hide formula {}.",
                    inAntec ? HIDE_LEFT : HIDE_RIGHT, sf);
                return current;
            }
            SchemaVariable schema = hideTaclet.collectSchemaVars().iterator().next();
            var services = goal.proof().getServices();
            TacletApp app = PosTacletApp.createPosTacletApp(hideTaclet, new MatchConditions(),
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), inAntec), services);
            app = app.addCheckedInstantiation(schema, (JTerm) sf.formula(), services, true);
            return current.apply(app).iterator().next();
        }
    }
}
