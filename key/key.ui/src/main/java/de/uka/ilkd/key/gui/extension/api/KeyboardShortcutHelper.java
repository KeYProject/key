package de.uka.ilkd.key.gui.extension.api;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.GoalList;
import de.uka.ilkd.key.gui.InfoView;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.sourceview.SourceView;

import javax.swing.*;
import java.util.Collection;
import java.util.Collections;
import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
public class KeyboardShortcutHelper implements KeYGuiExtension.KeyboardShortcuts {
    @Override
    public Collection<Action> getShortcuts(KeYMediator mediator, String componentId, JComponent component) {
        if (Objects.equals(SEQUENT_VIEW, componentId))
            return getShortcuts(mediator, (SequentView) component);
        if (Objects.equals(GOAL_LIST, componentId))
            return getShortcuts(mediator, (GoalList) component);
        if (Objects.equals(PROOF_TREE_VIEW, componentId))
            return getShortcuts(mediator, (ProofTreeView) component);
        if (Objects.equals(MAIN_WINDOW, componentId))
            return getShortcutsMainWindow(mediator, (JPanel) component);
        if (Objects.equals(INFO_VIEW, componentId))
            return getShortcuts(mediator, (InfoView) component);
        if (Objects.equals(STRATEGY_SELECTION_VIEW, componentId))
            return getShortcuts(mediator, (StrategySelectionView) component);
        if (Objects.equals(SOURCE_VIEW, componentId))
            return getShortcuts(mediator, (SourceView) component);

        return Collections.emptyList();
    }

    private Collection<Action> getShortcutsMainWindow(KeYMediator mediator, JPanel component) {
        return Collections.emptyList();
    }

    protected Collection<Action> getShortcuts(KeYMediator mediator, SequentView component) {
        return Collections.emptyList();
    }

    protected Collection<Action> getShortcuts(KeYMediator mediator, ProofTreeView component) {
        return Collections.emptyList();
    }

    protected Collection<Action> getShortcuts(KeYMediator mediator, StrategySelectionView component) {
        return Collections.emptyList();
    }

    protected Collection<Action> getShortcuts(KeYMediator mediator, InfoView component) {
        return Collections.emptyList();
    }

    protected Collection<Action> getShortcuts(KeYMediator mediator, SourceView component) {
        return Collections.emptyList();
    }

    protected Collection<Action> getShortcuts(KeYMediator mediator, GoalList component) {
        return Collections.emptyList();
    }
}
