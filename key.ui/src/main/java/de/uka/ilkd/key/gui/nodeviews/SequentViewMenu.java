/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.logic.NameCreationInfo;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PosInSequent;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * The menu shown by a {@link SequentViewListener} when the user clicks on a {@link SequentView}.
 *
 * @param <T> a type of {@link SequentView} on which this menu is shown.
 */
public class SequentViewMenu<T extends SequentView> extends JMenu {
    /**
     * The position of the selected term.
     */
    private @Nullable PosInSequent pos;

    /**
     * The sequent view associated with this menu.
     */
    private @NonNull T sequentView;

    private final KeyAction actionCopyToClipboard = new CopyToClipboardAction();
    private final KeyAction actionNameCreationInfo = new NameCreationInfoAction();

    /**
     * Creates an empty menu.
     */
    public SequentViewMenu() {
    }

    /**
     * Creates a new menu that displays all applicable actions at the given position.
     *
     * @param sequentView the SequentView that is the parent of this menu
     * @param pos the PosInSequent
     */
    SequentViewMenu(@NonNull T sequentView, @NonNull PosInSequent pos) {
        super();
        this.sequentView = sequentView;
        this.pos = pos;
    }

    /**
     * @return the position at which to show this menu.
     */
    protected @Nullable PosInSequent getPos() {
        return pos;
    }

    /**
     * @return the sequent view on which to show this menu.
     */
    @NonNull
    protected T getSequentView() {
        return sequentView;
    }

    /**
     * Add extension actions to this menu.
     * <p>
     * (see KeYSequentViewMenuExtension)
     * </p>
     *
     * @see KeYGuiExtensionFacade#getContextMenuItems
     */
    protected void addExtensionMenu() {
        List<Action> actions =
            KeYGuiExtensionFacade.getContextMenuItems(DefaultContextMenuKind.SEQUENT_VIEW, getPos(),
                getSequentView().getMainWindow().getMediator());

        for (Action action : actions) {
            add(action);
        }
    }

    /**
     * Adds an action to copy the selected term to the clipboard.
     */
    protected void addClipboardItem() {
        add(new JMenuItem(actionCopyToClipboard));
    }

    /**
     * Adds an action to show the name creation info to the clipboard.
     */
    protected void createNameCreationInfoSection() {
        add(new JMenuItem(actionNameCreationInfo));
    }


    class CopyToClipboardAction extends KeyAction {
        public CopyToClipboardAction() {
            setName("Copy to clipboard");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            GuiUtilities.copyHighlightToClipboard(sequentView, pos);
        }
    }

    class NameCreationInfoAction extends KeyAction {
        public NameCreationInfoAction() {
            setName("View name creation info");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            var t = pos.getPosInOccurrence().subTerm();
            ProgramVariable var = (ProgramVariable) t.op();
            ProgramElementName name = var.getProgramElementName();
            NameCreationInfo info = name.getCreationInfo();
            String message;
            if (info != null) {
                message = info.infoAsString();
            } else {
                message = "No information available.";
            }
            JOptionPane.showMessageDialog(null, message, "Name creation info",
                JOptionPane.INFORMATION_MESSAGE);
        }
    }
}
