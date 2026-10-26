/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.logic.NameCreationInfo;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PosInSequent;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The menu shown by a {@link SequentViewListener} when the user clicks on a {@link SequentView}.
 *
 * @param <T> a type of {@link SequentView} on which this menu is shown.
 */
@NullMarked
public class SequentViewMenu<T extends SequentView> extends JMenu {
    /**
     * The position of the selected term.
     */
    private @Nullable PosInSequent pos;

    /**
     * The sequent view associated with this menu; {@code null} for an empty menu that has not been
     * attached to a view yet.
     */
    private @Nullable T sequentView;

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
    protected @NonNull T getSequentView() {
        T view = sequentView;
        if (view == null) {
            // the menu is only used after its sequent view has been attached
            throw new NullPointerException("No sequent view available.");
        }
        return view;
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
            KeYGuiExtensionFacade.getContextMenuItems(ContextMenuKind.SEQUENT_VIEW, getPos(),
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
        /**
         * The action-configuration setters are called on {@code this} while the receiver is still
         * under initialization (EISOP initialization check); safe here, suppressed with a scoped
         * key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public CopyToClipboardAction() {
            setName("Copy to clipboard");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            PosInSequent currentPos = pos;
            if (currentPos == null) {
                // the copy action is only enabled when a term is selected
                throw new NullPointerException("No position available.");
            }
            GuiUtilities.copyHighlightToClipboard(getSequentView(), currentPos);
        }
    }

    class NameCreationInfoAction extends KeyAction {
        /**
         * The action-configuration setters are called on {@code this} while the receiver is still
         * under initialization (EISOP initialization check); safe here, suppressed with a scoped
         * key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public NameCreationInfoAction() {
            setName("View name creation info");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            PosInSequent currentPos = pos;
            if (currentPos == null) {
                // the info action is only enabled when a term is selected
                throw new NullPointerException("No position available.");
            }
            PosInOccurrence occurrence = currentPos.getPosInOccurrence();
            if (occurrence == null) {
                // the info action is only enabled when a term is selected
                throw new NullPointerException("No occurrence available.");
            }
            var t = occurrence.subTerm();
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
