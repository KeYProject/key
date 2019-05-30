package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.EnumSet;

import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.ext.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.ext.KeYSequentViewMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYSequentViewMenuExtension.SequentViewMenuType;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.logic.NameCreationInfo;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * The menu shown by a {@link SequentViewListener} when the user clicks on a {@link SequentView}.
 *
 * @param <T> a type of {@link SequentView} on which this menu is shown.
 */
public abstract class SequentViewMenu<T extends SequentView> extends JMenu {

    private static final String COPY_TO_CLIPBOARD = "Copy to clipboard";
    private static final String NAME_CREATION_INFO = "View name creation info";

    private PosInSequent pos;
    private T sequentView;
    /**
     * Creates an empty menu.
     */
    public SequentViewMenu() { }

    /**
     * Creates a new menu that displays all applicable actions at the given
     * position.
     *
     * @param sequentView the SequentView that is the parent of this menu
     * @param pos         the PosInSequent
     */
    SequentViewMenu(T sequentView, PosInSequent pos) {
        super();
        this.sequentView = sequentView;
        this.pos = pos;

        assert sequentView != null;
        assert pos != null;
    }

    /**
     *
     * @return the position at which to show this menu.
     */
    protected PosInSequent getPos() {
        return pos;
    }

    /**
     *
     * @return the sequent view on which to show this menu.
     */
    protected T getSequentView() {
        return sequentView;
    }

    /**
     * Add extension actions to this menu.
     *
     * @see KeYSequentViewMenuExtension
     * @see KeYGuiExtensionFacade#getSequentViewMenuActions(
     *  de.uka.ilkd.key.gui.MainWindow, PosInSequent, EnumSet)
     */
    protected void addExtensionMenu() {
        JMenu extensionMenu =
                KeYGuiExtensionFacade.createSequentViewMenu(
                        getSequentView().getMainWindow(),
                        getPos(),
                        EnumSet.of(SequentViewMenuType.of(getClass())));

        for (Component el : extensionMenu.getMenuComponents()) {
            add(el);
        }
    }

    /**
     * Adds an action to copy the selected term to the clipboard.
     *
     * @param control the action listener for the action.
     */
    protected void addClipboardItem(MenuControl control) {
        JMenuItem item = new JMenuItem(COPY_TO_CLIPBOARD);
        item.addActionListener(control);
        add(item);
    }

    /**
     * Adds an action to show the name creation info to the clipboard.
     *
     * @param control the action listener for the action.
     */
    protected void createNameCreationInfoSection(MenuControl control) {
        JMenuItem item = new JMenuItem(NAME_CREATION_INFO);
        item.addActionListener(control);
        add(item);
    }

    /**
     * The action listener for the actions in this menu.
     */
    protected class MenuControl implements ActionListener {

        @Override
        public void actionPerformed(ActionEvent e) {
            if (((JMenuItem) e.getSource()).getText()
                    .startsWith(COPY_TO_CLIPBOARD)) {
                GuiUtilities.copyHighlightToClipboard(sequentView, pos);
            } else if (((JMenuItem) e.getSource()).getText().
                    startsWith("View name creation info")) {
                Term t = pos.getPosInOccurrence().subTerm();
                ProgramVariable var = (ProgramVariable) t.op();
                ProgramElementName name = var.getProgramElementName();
                NameCreationInfo info = name.getCreationInfo();
                String message;
                if (info != null) {
                    message = info.infoAsString();
                } else {
                    message = "No information available.";
                }
                JOptionPane.showMessageDialog(null,
                        message,
                        "Name creation info",
                        JOptionPane.INFORMATION_MESSAGE);
            }
        }

    }
}
