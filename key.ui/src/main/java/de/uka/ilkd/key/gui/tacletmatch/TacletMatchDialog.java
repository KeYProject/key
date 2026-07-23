/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.*;

import de.uka.ilkd.key.control.InstantiationFileHandler;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ApplyTacletDialog;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog for completing and applying an interactively selected taclet.
 *
 * <p>
 * Per instantiation alternative it shows a {@link MatchInfoPanel} (how the find matched and the
 * bindings it determined), an {@link SVInstantiationPanel} (the schema variables left to
 * instantiate), an {@link AssumesSelectionPanel} (choose or type the {@code \assumes}
 * instantiation) and a {@link ResultPreviewPanel} (the resulting sequents). The inputs and the
 * preview are laid out in a responsive split that collapses to tabs when the window is narrow.
 *
 * <p>
 * In-place highlighting of each schema variable inside the matched term is a planned follow-up.
 */
public class TacletMatchDialog extends ApplyTacletDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(TacletMatchDialog.class);

    private static final long serialVersionUID = 1L;

    /** the goal the rule application is performed on */
    private final Goal goal;

    private final MainWindow mainWindow;

    /** one schema-variable instantiation panel per instantiation alternative */
    private final SVInstantiationPanel[] svPanels;

    /**
     * the assumptions panel per alternative, or {@code null} if the taclet has no assumes
     */
    private final AssumesSelectionPanel[] ifPanels;

    /** the result preview panel per alternative */
    private final ResultPreviewPanel[] previews;

    /** the tabbed pane selecting between instantiation alternatives */
    private JTabbedPane alternatives;

    /** single-line footer status (icon + message) */
    private JLabel statusLabel;

    public TacletMatchDialog(MainWindow parent, TacletInstantiationModel[] model, Goal goal,
            KeYMediator mediator) {
        super(parent, model, mediator);
        setName("tacletMatchDlgNext");
        this.mainWindow = parent;
        this.goal = goal;
        this.svPanels = new SVInstantiationPanel[model.length];
        this.ifPanels = new AssumesSelectionPanel[model.length];
        this.previews = new ResultPreviewPanel[model.length];

        for (TacletInstantiationModel aModel : model) {
            aModel.prepareUnmatchedInstantiation();
        }

        layoutDialog();
        pack();

        mainWindow.loadPreferences(this);
        positionDialog(parent);
        setVisible(true);
    }

    /**
     * where the dialog was last closed, remembered for this session only (deliberately not
     * persisted: on a restart the main window may sit elsewhere, so a stale absolute position would
     * be worse than a fresh placement beside the sequent).
     */
    private static Point sessionLocation;

    /**
     * Places the dialog so it does not sit on top of the sequent view. The user frequently needs to
     * read a variable name off the sequent, or drag a sub-term from it onto a field, so covering it
     * is exactly what to avoid. Within a session the last position the user moved it to is reused;
     * otherwise the dialog is put in the free space beside the sequent view, falling back to the
     * screen edge that leaves the most of the sequent visible. Either way it ends up fully on
     * screen.
     */
    private void positionDialog(MainWindow parent) {
        Rectangle screen = usableScreen(parent);
        Point target = sessionLocation != null ? sessionLocation : besideSequent(parent, screen);
        // keep the window fully on screen (the remembered spot may be off a since-changed screen)
        int x = Math.max(screen.x, Math.min(target.x, screen.x + screen.width - getWidth()));
        int y = Math.max(screen.y, Math.min(target.y, screen.y + screen.height - getHeight()));
        setLocation(x, y);
    }

    /** a spot beside the sequent view (right, else left, else the roomier screen edge). */
    private Point besideSequent(MainWindow parent, Rectangle screen) {
        Rectangle avoid = sequentBoundsOnScreen(parent);
        int gap = 8;
        int w = getWidth();
        int rightX = avoid.x + avoid.width + gap;
        int leftX = avoid.x - gap - w;
        int x;
        if (rightX + w <= screen.x + screen.width) {
            x = rightX; // free space to the right of the sequent
        } else if (leftX >= screen.x) {
            x = leftX; // free space to the left of the sequent
        } else {
            // the sequent leaves no room beside it: dock to the edge with more space, so at least
            // that much of the sequent stays visible
            int roomRight = screen.x + screen.width - (avoid.x + avoid.width);
            int roomLeft = avoid.x - screen.x;
            x = roomRight >= roomLeft ? screen.x + screen.width - w : screen.x;
        }
        return new Point(x, avoid.y); // align with the top of the sequent (caller clamps to screen)
    }

    /** the sequent view's rectangle on screen, or the whole main window if it is not showing. */
    private Rectangle sequentBoundsOnScreen(MainWindow parent) {
        Component seq = parent.getGoalView();
        if (seq != null && seq.isShowing()) {
            return new Rectangle(seq.getLocationOnScreen(), seq.getSize());
        }
        return parent.getBounds();
    }

    /** the usable bounds (minus taskbar/menubar insets) of the screen the main window is on. */
    private static Rectangle usableScreen(Window on) {
        GraphicsConfiguration gc = on.getGraphicsConfiguration();
        Rectangle b = gc.getBounds();
        Insets in = Toolkit.getDefaultToolkit().getScreenInsets(gc);
        return new Rectangle(b.x + in.left, b.y + in.top,
            b.width - in.left - in.right, b.height - in.top - in.bottom);
    }

    private void layoutDialog() {
        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(createInstantiationPanel(), BorderLayout.CENTER);
        getContentPane().add(createFooter(), BorderLayout.SOUTH);
    }

    private JComponent createInstantiationPanel() {
        if (model.length == 1) {
            // single match: show its content directly, no tab strip
            return buildAlternative(0);
        }

        alternatives = new JTabbedPane();
        for (int i = 0; i < model.length; i++) {
            alternatives.addTab("Match " + (i + 1) + " of " + model.length, buildAlternative(i));
        }
        alternatives.addChangeListener(e -> refreshStatus(current()));
        return alternatives;
    }

    /** a compact footer: status icon + message on the left, cancel/apply on the right. */
    private JComponent createFooter() {
        JPanel footer = new JPanel(new BorderLayout(12, 0));
        TmStyle.styleFooter(footer);

        statusLabel = new JLabel(" ");
        footer.add(statusLabel, BorderLayout.WEST);

        JPanel buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT, 8, 0));
        buttons.setOpaque(false);
        ButtonListener listener = new ButtonListener();
        cancelButton.addActionListener(listener);
        applyButton.addActionListener(listener);
        buttons.add(applyButton);
        buttons.add(cancelButton);
        footer.add(buttons, BorderLayout.EAST);

        setStatus(model[current()].getStatusString());
        return footer;
    }

    /**
     * builds the instantiation content (match overview, schema variables, assumptions) for one
     * instantiation alternative.
     */
    private JComponent buildAlternative(int i) {
        // inputs: match overview, schema variables, assumptions
        WidthTrackingPanel inputs = new WidthTrackingPanel();
        inputs.setLayout(new BoxLayout(inputs, BoxLayout.Y_AXIS));

        addSection(inputs, new MatchInfoPanel(model[i], mediator));

        SVInstantiationPanel svPanel =
            new SVInstantiationPanel(model[i], mediator, () -> refreshStatus(i));
        svPanels[i] = svPanel;
        addSection(inputs, svPanel);

        if (!model[i].application().taclet().assumesSequent().isEmpty()) {
            AssumesSelectionPanel assumes =
                new AssumesSelectionPanel(model[i], mediator, () -> refreshStatus(i));
            ifPanels[i] = assumes;
            addSection(inputs, assumes);
        }

        // preview, on the other side of the split
        WidthTrackingPanel previewPane = new WidthTrackingPanel();
        previewPane.setLayout(new BoxLayout(previewPane, BoxLayout.Y_AXIS));
        ResultPreviewPanel preview = new ResultPreviewPanel(model[i], mediator, goal);
        previews[i] = preview;
        addSection(previewPane, preview);

        JScrollPane inputsScroll = scroll(inputs, 540);
        JScrollPane previewScroll = scroll(previewPane, 340);
        return new ResponsiveSplit(inputsScroll, "Instantiate", previewScroll, "Result preview");
    }

    private static JScrollPane scroll(JComponent view, int preferredWidth) {
        JScrollPane scroll = new JScrollPane(view);
        scroll.setBorder(null);
        scroll.setPreferredSize(new Dimension(preferredWidth, 520));
        scroll.getVerticalScrollBar().setUnitIncrement(16);
        return scroll;
    }

    /**
     * adds a section so it fills the available width. The section is wrapped in a BorderLayout
     * panel
     * so that, regardless of the section's own layout, every section reports the same alignment to
     * the surrounding BoxLayout (which otherwise refuses to stretch components of mixed alignment).
     */
    private static void addSection(JComponent container, JComponent section) {
        JPanel wrap = new JPanel(new BorderLayout());
        wrap.setOpaque(false);
        wrap.add(section, BorderLayout.CENTER);
        container.add(wrap);
    }

    /**
     * A vertically-scrolling panel that always fills the viewport width, so its children stretch to
     * the full width instead of leaving empty space on the right.
     */
    private static class WidthTrackingPanel extends JPanel implements Scrollable {
        private static final long serialVersionUID = 1L;

        @Override
        public Dimension getPreferredScrollableViewportSize() {
            return getPreferredSize();
        }

        @Override
        public int getScrollableUnitIncrement(Rectangle visible, int orientation, int direction) {
            return 16;
        }

        @Override
        public int getScrollableBlockIncrement(Rectangle visible, int orientation, int direction) {
            return Math.max(16, visible.height - 24);
        }

        @Override
        public boolean getScrollableTracksViewportWidth() {
            return true;
        }

        @Override
        public boolean getScrollableTracksViewportHeight() {
            return false;
        }
    }

    /** refreshes the status display and result preview from the given alternative if selected */
    private void refreshStatus(int idx) {
        if (idx == current()) {
            setStatus(model[idx].getStatusString());
            if (previews[idx] != null) {
                previews[idx].requestUpdate();
            }
        }
    }

    @Override
    protected void setStatus(String s) {
        if (statusLabel == null) {
            return;
        }
        if (s == null || s.isEmpty()) {
            statusLabel.setText(" ");
            statusLabel.setIcon(null);
            statusLabel.setToolTipText(null);
            return;
        }
        int nl = s.indexOf('\n');
        String firstLine = nl >= 0 ? s.substring(0, nl) : s;

        FontAwesomeSolid glyph;
        Color color;
        if (s.startsWith("Instantiation is OK")) {
            glyph = FontAwesomeSolid.CHECK_CIRCLE;
            color = new Color(0x1D9E75);
        } else if (s.startsWith("Rule is not applicable")) {
            glyph = FontAwesomeSolid.TIMES_CIRCLE;
            color = new Color(0xC0392B);
        } else {
            glyph = FontAwesomeSolid.EXCLAMATION_CIRCLE;
            color = new Color(0xBA7517);
        }
        statusLabel.setIcon(IconFontSwing.buildIcon(glyph, 14f, color));
        statusLabel.setIconTextGap(6);
        statusLabel.setText(firstLine);
        statusLabel.setForeground(color);
        statusLabel.setToolTipText(nl >= 0 ? "<html>" + s.replace("\n", "<br>") + "</html>" : null);
    }

    @Override
    protected int current() {
        return alternatives == null ? 0 : alternatives.getSelectedIndex();
    }

    @Override
    protected void pushAllInputToModel() {
        int i = current();
        if (ifPanels[i] != null) {
            ifPanels[i].pushAllInputToModel();
        }
        if (svPanels[i] != null) {
            svPanels[i].pushAllInputToModel();
        }
    }

    @Override
    protected void closeDlg() {
        // remember the position for the rest of this session; savePreferences persists the size
        sessionLocation = getLocation();
        if (mainWindow != null) {
            mainWindow.savePreferences(this);
        }
        super.closeDlg();
    }

    private class ButtonListener implements ActionListener {
        @Override
        public void actionPerformed(ActionEvent e) {
            if (e.getSource() == cancelButton) {
                closeDialog();
            } else if (e.getSource() == applyButton) {
                try {
                    pushAllInputToModel();
                    TacletApp app = model[current()].createTacletApp();
                    if (app == null) {
                        JOptionPane.showMessageDialog(TacletMatchDialog.this,
                            "Could not apply rule",
                            "Rule Application Failure", JOptionPane.ERROR_MESSAGE);
                        return;
                    }
                    mediator().getUI().getProofControl().applyInteractive(app, goal);
                } catch (Exception exc) {
                    LOGGER.error("Taclet application failed", exc);
                    IssueDialog.showExceptionDialog(TacletMatchDialog.this, exc);
                    return;
                }
                InstantiationFileHandler.saveListFor(model[current()]);
                closeDialog();
            }
        }

        private void closeDialog() {
            closeDlg();
            setVisible(false);
            dispose();
        }
    }
}
