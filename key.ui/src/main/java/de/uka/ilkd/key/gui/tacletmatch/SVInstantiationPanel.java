/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.dnd.*;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.JTextComponent;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.PosInSequentTransferable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;

import org.key_project.logic.op.sv.SchemaVariable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Panel for the schema variables the user still has to instantiate: those occurring only in
 * {@code \add}/{@code \replacewith}/{@code \assumes}, not determined by the find match (the
 * find-determined ones are shown read-only in the {@link MatchInfoPanel}). Each row offers the
 * proposal pre-filled by the model, accepts drag-and-drop of a sub-term from the sequent, and
 * writes
 * its input back to the shared {@link TacletFindModel}, refreshing the dialog status on change.
 */
public class SVInstantiationPanel extends JPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(SVInstantiationPanel.class);

    private static final long serialVersionUID = 1L;

    private final TacletFindModel tableModel;
    private final KeYMediator mediator;
    private final Runnable onChange;

    /** the editable rows: the model-row index and the field carrying its input */
    private record Row(int modelRow, SvField field) {
    }

    private final List<Row> rows = new ArrayList<>();

    /** debounce for refreshing the status/preview while typing */
    private Timer refreshTimer;

    public SVInstantiationPanel(TacletInstantiationModel model, KeYMediator mediator,
            Runnable onChange) {
        this.tableModel = model.tableModel();
        this.mediator = mediator;
        this.onChange = onChange;

        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        setBorder(TmStyle.section("Instantiate schema variables"));
        build();
    }

    /** above this many editable variables, lay the fields out in two columns */
    private static final int TWO_COLUMN_THRESHOLD = 3;

    private void build() {
        List<JComponent> rowComps = new ArrayList<>();
        int colorIndex = 0;
        for (int r = 0; r < tableModel.getRowCount(); r++) {
            if (!tableModel.isCellEditable(r, 1)) {
                continue;
            }
            SchemaVariable sv = (SchemaVariable) tableModel.getValueAt(r, 0);
            Object value = tableModel.getValueAt(r, 1);

            SvField field = new SvField(value == null ? "" : value.toString());
            field.area.addFocusListener(new FocusAdapter() {
                @Override
                public void focusLost(FocusEvent e) {
                    pushAndRefresh();
                }
            });
            // refresh status and preview after a short typing pause, not only on focus change
            field.area.getDocument().addDocumentListener(new DocumentListener() {
                @Override
                public void insertUpdate(DocumentEvent e) {
                    scheduleRefresh();
                }

                @Override
                public void removeUpdate(DocumentEvent e) {
                    scheduleRefresh();
                }

                @Override
                public void changedUpdate(DocumentEvent e) {
                    scheduleRefresh();
                }
            });
            installDropTarget(field);

            rows.add(new Row(r, field));
            rowComps.add(rowComponent(SvPalette.chip(sv.name().toString(), colorIndex++),
                field.component));
        }

        if (rowComps.isEmpty()) {
            JLabel none = new JLabel("All schema variables are determined by the match.");
            none.setForeground(UIManager.getColor("Label.disabledForeground"));
            add(none);
            return;
        }

        // anchor the content to the top so the surrounding layout cannot stretch it; individual
        // fields can then grow when expanded
        setLayout(new BorderLayout());
        JPanel content = new JPanel();
        content.setOpaque(false);
        if (rowComps.size() > TWO_COLUMN_THRESHOLD) {
            // many variables: two columns to stay compact. GridBag (fill horizontal, anchored top)
            // so expanding one field grows only its own cell, not the whole row of fields.
            content.setLayout(new GridBagLayout());
            GridBagConstraints gc = new GridBagConstraints();
            gc.fill = GridBagConstraints.HORIZONTAL;
            gc.anchor = GridBagConstraints.NORTHWEST;
            gc.weightx = 1.0;
            int col = 0;
            int row = 0;
            for (JComponent rc : rowComps) {
                gc.gridx = col;
                gc.gridy = row;
                gc.insets = new Insets(2, 0, 2, col == 0 ? 16 : 0);
                content.add(rc, gc);
                if (++col == 2) {
                    col = 0;
                    row++;
                }
            }
        } else {
            content.setLayout(new BoxLayout(content, BoxLayout.Y_AXIS));
            rowComps.forEach(content::add);
        }
        add(content, BorderLayout.NORTH);
    }

    private JComponent rowComponent(JComponent chip, JComponent field) {
        JPanel p = new JPanel(new BorderLayout(6, 0));
        p.setOpaque(false);
        p.setBorder(new EmptyBorder(2, 0, 2, 0));

        JPanel west = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 0));
        west.setOpaque(false);
        west.add(chip);
        west.add(new JLabel("↦"));

        p.add(west, BorderLayout.WEST);
        p.add(field, BorderLayout.CENTER);
        return p;
    }

    /** writes every field's text back to the model. */
    public void pushAllInputToModel() {
        for (Row row : rows) {
            tableModel.setValueAt(row.field().getText(), row.modelRow(), 1);
        }
    }

    private void pushAndRefresh() {
        pushAllInputToModel();
        if (onChange != null) {
            onChange.run();
        }
    }

    /** debounces {@link #pushAndRefresh()} so typing updates the status/preview after a pause. */
    private void scheduleRefresh() {
        if (refreshTimer == null) {
            refreshTimer = new Timer(300, e -> pushAndRefresh());
            refreshTimer.setRepeats(false);
        }
        refreshTimer.restart();
    }

    private void installDropTarget(SvField field) {
        new DropTarget(field.area, new DropTargetAdapter() {
            @Override
            public void dragEnter(DropTargetDragEvent event) {
                field.setDropHighlight(true);
            }

            @Override
            public void dragExit(DropTargetEvent event) {
                field.setDropHighlight(false);
            }

            @Override
            public void drop(DropTargetDropEvent event) {
                field.setDropHighlight(false);
                Transferable t = event.getTransferable();
                try {
                    if (t.isDataFlavorSupported(
                        PosInSequentTransferable.POS_IN_SEQUENT_TRANSFER)) {
                        event.acceptDrop(DnDConstants.ACTION_MOVE);
                        PosInSequent pis = (PosInSequent) t.getTransferData(
                            PosInSequentTransferable.POS_IN_SEQUENT_TRANSFER);
                        JTerm term = (JTerm) pis.getPosInOccurrence().subTerm();
                        insertAtCaret(field.area, printTerm(term));
                        event.getDropTargetContext().dropComplete(true);
                    } else if (t.isDataFlavorSupported(DataFlavor.stringFlavor)) {
                        event.acceptDrop(DnDConstants.ACTION_MOVE);
                        insertAtCaret(field.area,
                            (String) t.getTransferData(DataFlavor.stringFlavor));
                        event.getDropTargetContext().dropComplete(true);
                    } else {
                        event.rejectDrop();
                        return;
                    }
                    field.autoExpandIfMultiline();
                    pushAndRefresh();
                } catch (Exception ex) {
                    LOGGER.warn("Drop onto schema-variable field failed", ex);
                    event.rejectDrop();
                }
            }
        });
    }

    private static void insertAtCaret(JTextComponent field, String s) {
        if (s == null) {
            return;
        }
        try {
            field.getDocument().insertString(field.getCaretPosition(), s, null);
        } catch (BadLocationException e) {
            field.setText(field.getText() + s);
        }
    }

    /**
     * An editable instantiation field that shows long, possibly multi-line content nicely: a single
     * line by default, expandable to several lines (scrolling beyond) via a small toggle, so a
     * dropped term does not blow up the dialog.
     */
    private final class SvField {
        private final JTextArea area = new JTextArea() {
            @Override
            protected void paintComponent(Graphics g) {
                super.paintComponent(g);
                // a hint that the field accepts a dropped sub-term, shown only while
                // empty/unfocused
                if (getText().isEmpty() && !isFocusOwner()) {
                    g.setColor(TmStyle.muted());
                    g.setFont(getFont());
                    Insets in = getInsets();
                    g.drawString("drop a term or type…", in.left + 1,
                        in.top + g.getFontMetrics().getAscent());
                }
            }
        };
        private final JScrollPane scroll;
        private final JButton toggle;
        private final JPanel component;
        private final Border defaultBorder;
        private boolean expanded;

        SvField(String value) {
            area.setText(value);
            area.setFont(TmStyle.mono(area));
            area.setLineWrap(true);
            area.setWrapStyleWord(true);
            // keep Tab / Shift-Tab as focus traversal instead of inserting a tab character
            area.setFocusTraversalKeys(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS,
                Set.of(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, 0)));
            area.setFocusTraversalKeys(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS,
                Set.of(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, InputEvent.SHIFT_DOWN_MASK)));
            area.addFocusListener(new FocusAdapter() {
                @Override
                public void focusGained(FocusEvent e) {
                    area.repaint();
                }

                @Override
                public void focusLost(FocusEvent e) {
                    area.repaint();
                }
            });

            defaultBorder = UIManager.getBorder("TextField.border");
            scroll = new JScrollPane(area, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
            scroll.setBorder(defaultBorder);

            toggle = TmStyle.disclosure("the whole instantiation");
            toggle.addActionListener(e -> setExpanded(!expanded));

            // the inline field stays small; an edit icon (the same one the error dialog uses) opens
            // a larger, resizable editor for comfortably entering long instantiations
            JButton edit = new JButton(IconFactory.editFile(12));
            edit.setFocusable(false);
            edit.setBorderPainted(false);
            edit.setContentAreaFilled(false);
            edit.setMargin(new Insets(0, 3, 0, 3));
            edit.setToolTipText("Edit in a larger, resizable window");
            edit.addActionListener(e -> openInEditor());

            JPanel controls = new JPanel(new FlowLayout(FlowLayout.LEFT, 0, 0));
            controls.setOpaque(false);
            controls.add(toggle);
            controls.add(edit);

            JPanel east = new JPanel(new BorderLayout());
            east.setOpaque(false);
            east.add(controls, BorderLayout.NORTH);

            component = new JPanel(new BorderLayout(4, 0));
            component.setOpaque(false);
            component.add(scroll, BorderLayout.CENTER);
            component.add(east, BorderLayout.EAST);
            updateHeight();
        }

        String getText() {
            return area.getText();
        }

        void autoExpandIfMultiline() {
            if (!expanded && area.getText().indexOf('\n') >= 0) {
                setExpanded(true);
            }
        }

        private void setExpanded(boolean e) {
            expanded = e;
            TmStyle.setDisclosure(toggle, e);
            updateHeight();
            revalidate();
            repaint();
        }

        void setDropHighlight(boolean on) {
            Color hl = UIManager.getColor("Component.focusColor");
            scroll.setBorder(on
                    ? BorderFactory.createLineBorder(hl != null ? hl : new Color(0x378ADD), 2)
                    : defaultBorder);
        }

        /**
         * opens the field's content in a larger, resizable editor window; on OK the edited text
         * replaces the field's content (which refreshes the status/preview as usual).
         */
        private void openInEditor() {
            Window owner = SwingUtilities.getWindowAncestor(component);
            JDialog dlg = new JDialog(owner, "Edit instantiation",
                Dialog.ModalityType.APPLICATION_MODAL);

            JTextArea ta = new JTextArea(area.getText(), 14, 60);
            ta.setFont(TmStyle.mono(ta));
            ta.setLineWrap(true);
            ta.setWrapStyleWord(true);

            JButton ok = new JButton("OK");
            JButton cancel = new JButton("Cancel");
            ok.addActionListener(e -> {
                area.setText(ta.getText());
                autoExpandIfMultiline();
                dlg.dispose();
            });
            cancel.addActionListener(e -> dlg.dispose());

            JPanel buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT, 8, 0));
            buttons.setOpaque(false);
            buttons.add(cancel);
            buttons.add(ok);

            JPanel content = new JPanel(new BorderLayout(0, 8));
            content.setBorder(new EmptyBorder(8, 8, 8, 8));
            content.add(new JScrollPane(ta), BorderLayout.CENTER);
            content.add(buttons, BorderLayout.SOUTH);
            dlg.setContentPane(content);
            dlg.getRootPane().setDefaultButton(ok);
            dlg.pack();
            dlg.setMinimumSize(new Dimension(320, 200));
            dlg.setLocationRelativeTo(owner);
            SwingUtilities.invokeLater(ta::requestFocusInWindow);
            dlg.setVisible(true);
        }

        private void updateHeight() {
            int rowH = area.getFontMetrics(area.getFont()).getHeight();
            int rows = expanded ? 5 : 1;
            Insets in = scroll.getInsets();
            scroll.setVerticalScrollBarPolicy(expanded
                    ? ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED
                    : ScrollPaneConstants.VERTICAL_SCROLLBAR_NEVER);
            scroll.setPreferredSize(new Dimension(140, rows * rowH + in.top + in.bottom + 4));
        }
    }

    /**
     * prints a term for insertion into an instantiation field. A few notations the parser cannot
     * yet
     * round-trip are disabled, mirroring the classic dialog, so the result re-parses.
     */
    private String printTerm(JTerm term) {
        final Services services = mediator.getServices();
        final NotationInfo ni = new NotationInfo();
        final JTerm t = TermLabelManager.removeIrrelevantLabels(term, services);
        LogicPrinter p = LogicPrinter.purePrinter(ni, services);
        boolean pretty = mediator.getNotationInfo().isPrettySyntax();
        ni.refresh(services, pretty, false, false);
        Map<Object, Notation> tbl = ni.getNotationTable();

        if (pretty) {
            final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
            tbl.remove(setLDT.getUnion());
            tbl.remove(setLDT.getIntersect());
            tbl.remove(setLDT.getSetMinus());
            tbl.remove(setLDT.getElementOf());
            tbl.remove(setLDT.getSubset());
            tbl.remove(IObserverFunction.class);
            tbl.remove(IProgramMethod.class);
        }

        p.printTerm(t);
        return p.result();
    }
}
