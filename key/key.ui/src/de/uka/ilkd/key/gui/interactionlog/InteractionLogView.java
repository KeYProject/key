package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.Markdown;
import de.uka.ilkd.key.gui.fonticons.FontAwesome;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.interactionlog.algo.MarkdownExport;
import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import sun.swing.DefaultLookup;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.awt.dnd.DropTarget;
import java.awt.dnd.DropTargetAdapter;
import java.awt.dnd.DropTargetDropEvent;
import java.awt.event.*;
import java.io.File;
import java.io.IOException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Optional;

public class InteractionLogView extends JPanel implements InteractionRecorderListener {
    private static final float SMALL_ICON_SIZE = 16f;
    private final ExportUlbrichScriptAction actionExportProofScript = new ExportUlbrichScriptAction();
    private final ExportKPSAction actionKPSExport = new ExportKPSAction();
    private final SaveAction actionSave = new SaveAction();
    private final LoadAction actionLoad = new LoadAction();
    private final AddUserNoteAction actionAddUserNote = new AddUserNoteAction();
    private final ToggleFavouriteAction actionToggleFavourite = new ToggleFavouriteAction();
    private final JumpIntoTreeAction actionJumpIntoTree = new JumpIntoTreeAction();
    private final TryReapplyAction actionTryReapply = new TryReapplyAction();
    private final ExportMarkdownAction actionExportMarkdown = new ExportMarkdownAction();
    private final ShowExtendedActionsAction actionShowExtended = new ShowExtendedActionsAction();

    private final InteractionRecorder recorder = new InteractionRecorder();


    private final JList<Interaction> listInteraction = new JList<>();
    private final JComboBox<InteractionLog> interactionLogSelection = new JComboBox<>();
    private final DefaultListModel<Interaction> interactionListModel = new DefaultListModel<>();
    private final Services services;
    private Proof currentProof;


    public InteractionLogView(MainWindow mainWindow, KeYMediator mediator) {
        // register the recorder in the proof control
        mainWindow.getUserInterface().getProofControl().addInteractionListener(recorder);
        mainWindow.getUserInterface().getProofControl().addAutoModeListener(recorder);
        services = mediator.getServices();

        listInteraction.setModel(interactionListModel);
        listInteraction.setCellRenderer(new InteractionCellRenderer());

        JToolBar panelButtons = new JToolBar();
        panelButtons.add(interactionLogSelection);
        JButton btnLoad = new JButton(actionLoad);
        JButton btnSave = new JButton(actionSave);
        JButton btnExport = new JButton(actionExportProofScript);
        JButton btnAddNote = new JButton(actionAddUserNote);

        btnExport.setHideActionText(true);
        btnSave.setHideActionText(true);
        btnAddNote.setHideActionText(true);
        btnLoad.setHideActionText(true);

        panelButtons.add(btnLoad);
        panelButtons.add(btnSave);
        panelButtons.add(Box.createHorizontalGlue());
        panelButtons.add(actionAddUserNote);
        panelButtons.addSeparator();
        panelButtons.add(actionShowExtended);

        JPopupMenu popup = new JPopupMenu();
        popup.add(new JMenuItem(actionToggleFavourite));
        popup.add(new JMenuItem(actionJumpIntoTree));
        popup.add(new JMenuItem(actionTryReapply));
        popup.addSeparator();
        popup.add(new JMenuItem(actionAddUserNote));
        listInteraction.setComponentPopupMenu(popup);

        recorder.addListener(this);

        interactionLogSelection.setModel(recorder.getLoadedInteractionLogs());
        interactionLogSelection.addActionListener(this::handleSelectionChange);
        interactionLogSelection.setModel(recorder.getLoadedInteractionLogs());

        listInteraction.addMouseMotionListener(new MouseMotionAdapter() {
            @Override
            public void mouseMoved(MouseEvent e) {
                JList l = (JList) e.getSource();
                ListModel m = l.getModel();
                int index = l.locationToIndex(e.getPoint());
                if (index > -1) {
                    Interaction inter = (Interaction) m.getElementAt(index);
                    l.setToolTipText("<html>" + MarkdownExport.getHtml(inter) + "</html>");
                }
            }
        });

        interactionLogSelection.setModel(recorder.getLoadedInteractionLogs());

        new DropTarget(listInteraction, 0, new DropTargetAdapter() {
            @Override
            public void drop(DropTargetDropEvent dtde) {
                Transferable tr = dtde.getTransferable();
                try {
                    Object textFlavour = tr.getTransferData(DataFlavor.stringFlavor);
                    dtde.acceptDrop(dtde.getDropAction());
                    dtde.dropComplete(true);
                    SwingUtilities.invokeLater(() -> actionAddUserNote.doAddNote(textFlavour.toString()));
                    return;
                } catch (UnsupportedFlavorException | IOException e) {
                    e.printStackTrace();
                }
                dtde.rejectDrop();
            }
        });

        setLayout(new BorderLayout());
        add(panelButtons, BorderLayout.NORTH);
        add(new JScrollPane(listInteraction));
        recorder.addListener(this);

        setBorder(BorderFactory.createTitledBorder("Interactions"));

        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                setCurrentProof(e.getSource().getSelectedProof());
            }
        });
        setCurrentProof(mediator.getSelectedProof());

    }

    private void handleSelectionChange(ActionEvent actionEvent) {
        InteractionLog selectedLog = getSelectedItem();
        updateList(selectedLog);
    }

    private InteractionLog getSelectedItem() {
        return (InteractionLog) interactionLogSelection.getSelectedItem();
    }


    private void setCurrentProof(Proof proof) {
        if (proof == null) return;
        currentProof = proof;
        recorder.get(currentProof);
        //rebuildList();
    }


    private void rebuildList() {
        InteractionLog currentInteractionLog = getSelectedItem();
        if (currentProof != null) {
            InteractionLog state = recorder.get(currentProof);
            updateList(state);
        }
    }

    private void updateList(InteractionLog interactionLog) {
        interactionListModel.clear();
        interactionLog.getInteractions().forEach(interactionListModel::addElement);
    }

    @Override
    public void onInteraction(Interaction interaction) {
        rebuildList();
    }

    public ExportUlbrichScriptAction getActionExportProofScript() {
        return actionExportProofScript;
    }

    public SaveAction getActionSave() {
        return actionSave;
    }

    public LoadAction getActionLoad() {
        return actionLoad;
    }

    public AddUserNoteAction getActionAddUserNote() {
        return actionAddUserNote;
    }

    public JumpIntoTreeAction getActionJumpIntoTree() {
        return actionJumpIntoTree;
    }

    public TryReapplyAction getActionTryReapply() {
        return actionTryReapply;
    }

    public InteractionRecorder getRecorder() {
        return recorder;
    }

    private class InteractionLogModelItem extends DefaultComboBoxModel<InteractionLog> {
    }

    private class ExportUlbrichScriptAction extends AbstractAction {
        ExportUlbrichScriptAction() {
            putValue(Action.NAME, "Export as Proof Script");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.FILE_EXPORT, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JOptionPane.showMessageDialog((Component) e.getSource(), "TODO");
            LogPrinter lp = new LogPrinter(services);
            InteractionLog state = recorder.get(currentProof);
            String ps = lp.print(state);
            System.out.println(ps);
        }
    }

    private class LoadAction extends AbstractAction {
        LoadAction() {
            putValue(Action.NAME, "Load");
            putValue(Action.SHORT_DESCRIPTION, "Load Interaction Log");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.TRUCK_LOADING, SMALL_ICON_SIZE));
            // new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_add.png")));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setFileFilter(new FileNameExtensionFilter(
                    "InteractionLog", "xml"));
            int returnValue = fileChooser.showOpenDialog(null);
            if (returnValue == JFileChooser.APPROVE_OPTION) {
                try {
                    File file = fileChooser.getSelectedFile();
                    recorder.readInteractionLog(file);
                    //addInteractionLog(importedLog);
                } catch (Exception exception) {
                    JOptionPane.showMessageDialog(null,
                            exception.getCause(),
                            "IOException",
                            JOptionPane.WARNING_MESSAGE);
                    exception.printStackTrace();
                }
            }
        }
    }

    private class SaveAction extends AbstractAction {
        SaveAction() {
            putValue(Action.NAME, "Save");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesome.SAVE, SMALL_ICON_SIZE));
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_save.png")));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setFileFilter(new FileNameExtensionFilter(
                    "InteractionLog", "xml"));
            int returnValue = fileChooser.showSaveDialog(null);
            if (returnValue == JFileChooser.APPROVE_OPTION) {
                InteractionLog activeInteractionLog = getSelectedItem();
                try {
                    InteractionLogFacade.storeInteractionLog(activeInteractionLog, fileChooser.getSelectedFile());
                } catch (Exception exception) {
                    JOptionPane.showMessageDialog(null,
                            exception.getCause(),
                            "IOException",
                            JOptionPane.WARNING_MESSAGE);
                    exception.printStackTrace();
                }
            }
        }
    }

    private class AddUserNoteAction extends AbstractAction {
        AddUserNoteAction() {
            super("Add Note");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesome.STICKY_NOTE, SMALL_ICON_SIZE));
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/book_add.png")));

        }

        @Override
        public void actionPerformed(ActionEvent e) {
            doAddNote("");
        }

        void doAddNote(String prefilled) {
            Optional<String> note = new MultiLineInputPrompt(InteractionLogView.this, prefilled).show();
            if (note.isPresent()) {
                UserNoteInteraction interaction = new UserNoteInteraction(note.get());
                InteractionLog interactionLog = (InteractionLog) interactionLogSelection.getSelectedItem();
                if (interactionLog.getInteractions() != null)
                    interactionLog.getInteractions().add(interaction);
                onInteraction(interaction);
            }

        }
    }

    private class ToggleFavouriteAction extends AbstractAction {
        ToggleFavouriteAction() {
            super("Toggle Fav");
            setName("Toggle Fav");
            putValue(Action.MNEMONIC_KEY, KeyEvent.VK_F);
            putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_M, InputEvent.CTRL_MASK));
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.HEART, SMALL_ICON_SIZE, Color.red));
            //    new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/heart.png")));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (listInteraction.getSelectedValue() != null) {
                listInteraction.getSelectedValue().setFavoured(!listInteraction.getSelectedValue().isFavoured());
            }
        }
    }

    private class JumpIntoTreeAction extends AbstractAction {
        JumpIntoTreeAction() {
            super("Jump into tree");
            putValue(SMALL_ICON, IconFontSwing.buildIcon(FontAwesome.CODE, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JOptionPane.showMessageDialog((Component) e.getSource(), "TODO");
        }
    }

    private class TryReapplyAction extends AbstractAction {
        TryReapplyAction() {
            putValue(NAME, "Re-apply action");
            putValue(SMALL_ICON, IconFontSwing.buildIcon(FontAwesome.APPER, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JOptionPane.showMessageDialog(null, "Not Implemented",
                    "A very expected error.", JOptionPane.ERROR_MESSAGE);
        }
    }

    private class ExportKPSAction extends AbstractAction {
        public ExportKPSAction() {
            super("Export as KPS …");
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into the KPS format.");
            putValue(Action.SMALL_ICON, IconFontSwing.buildIcon(FontAwesomeBold.CODE, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JOptionPane.showMessageDialog((Component) e.getSource(), "TODO");
        }
    }

    private class ExportMarkdownAction extends AbstractAction {
        public ExportMarkdownAction() {
            super("Export as markdown …");
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into a markdown file.");
            putValue(Action.SMALL_ICON, IconFontSwing.buildIcon(FontAwesomeBold.MARKDOWN, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JOptionPane.showMessageDialog((Component) e.getSource(), "TODO");
        }
    }

    private class ShowExtendedActionsAction extends AbstractAction {
        public ShowExtendedActionsAction() {
            super("More …");
            putValue(Action.SHORT_DESCRIPTION, "Shows further options");
            putValue(Action.SMALL_ICON, IconFontSwing.buildIcon(FontAwesomeBold.WRENCH, SMALL_ICON_SIZE));
        }

        public JPopupMenu createMenu() {
            JPopupMenu menu = new JPopupMenu(getName());
            menu.add(actionExportMarkdown);
            menu.add(actionExportProofScript);
            menu.add(actionKPSExport);
            return menu;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JComponent btn = (JComponent) e.getSource();
            JPopupMenu menu = createMenu();
            PointerInfo pi = MouseInfo.getPointerInfo();
            menu.show(btn, 0,0);
            //pi.getLocation().x, pi.getLocation().y);
        }
    }
}

class MultiLineInputPrompt {
    private final String text;
    private JComponent parent;
    private JDialog dialog;
    private String acceptedAnswer;

    public MultiLineInputPrompt(JComponent parent, String prefilled) {
        this.parent = parent;
        this.text = prefilled;
    }

    protected JDialog getDialog() {
        if (dialog == null) {
            dialog = new JDialog(JOptionPane.getFrameForComponent(parent));
            dialog.setModal(true);
            dialog.setTitle("Enter note...");

            JPanel root = new JPanel(new BorderLayout(10, 10));
            JPanel box = new JPanel(new FlowLayout(FlowLayout.CENTER));
            root.add(box, BorderLayout.SOUTH);
            JTextArea area = new JTextArea(text);
            JButton btnOk = new JButton("Ok");
            JButton btnCancel = new JButton("Cancel");
            box.add(btnOk);
            box.add(btnCancel);

            btnOk.addActionListener((evt) -> accept(area.getText()));
            btnCancel.addActionListener((evt) -> cancel());
            dialog.setDefaultCloseOperation(JDialog.HIDE_ON_CLOSE);
            dialog.addWindowListener(new WindowAdapter() {
                @Override
                public void windowClosed(WindowEvent e) {
                    cancel();
                }
            });
            dialog.setContentPane(root);

            root.add(new JScrollPane(area), BorderLayout.CENTER);

            dialog.setSize(300, 200);
            dialog.setLocationRelativeTo(parent);

        }
        return dialog;
    }

    private void cancel() {
        acceptedAnswer = null;
        getDialog().setVisible(false);
    }

    private void accept(String text) {
        acceptedAnswer = text;
        getDialog().setVisible(false);
    }

    public Optional<String> show() {
        getDialog().setVisible(true);
        return Optional.ofNullable(acceptedAnswer);
    }

    public void setParent(JComponent parent) {
        this.parent = parent;
    }
}

class InteractionCellRenderer extends JPanel implements ListCellRenderer<Interaction> {
    private static final DateFormat df = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
    private static final Color COLOR_FAVOURED = new Color(0xFFD373);
    private JLabel lblIconLeft = new JLabel(), lblIconRight = new JLabel(), lblText = new JLabel();
    private Icon iconHeart = IconFontSwing.buildIcon(FontAwesome.HEART, 16f, Color.RED);

    InteractionCellRenderer() {
        setLayout(new BorderLayout());
        add(lblIconLeft, BorderLayout.WEST);
        add(lblIconRight, BorderLayout.EAST);
        add(lblText);
    }

    @Override
    public Component getListCellRendererComponent(JList<? extends Interaction> list, Interaction value, int index, boolean isSelected, boolean cellHasFocus) {
        lblText.setText(
                value != null ?
                        df.format(value.getCreated()) + " " + value.toString() : "");
        lblIconRight.setIcon(value != null && value.isFavoured() ? iconHeart : null);
        //TODO
        setBorder(value != null && value.isFavoured() ? BorderFactory.createLineBorder(COLOR_FAVOURED) : null);

        setComponentOrientation(list.getComponentOrientation());

        if (isSelected) {
            setBackground(list.getSelectionBackground());
            setForeground(list.getSelectionForeground());
        } else {
            if (value != null) {
                setBackground(value.getGraphicalStyle().getBackgroundColor() != null ?
                        value.getGraphicalStyle().getBackgroundColor()
                        : list.getBackground());

                setForeground(value.getGraphicalStyle().getForegroundColor() != null ?
                        value.getGraphicalStyle().getForegroundColor()
                        : list.getForeground());
            }
        }

        lblIconRight.setForeground(getForeground());
        lblIconLeft.setForeground(getForeground());
        lblText.setForeground(getForeground());

        lblIconRight.setBackground(getBackground());
        lblIconLeft.setBackground(getBackground());
        lblText.setBackground(getBackground());


        setEnabled(list.isEnabled());
        setFont(list.getFont());

        Border border = null;
        if (cellHasFocus) {
            if (isSelected) {
                border = DefaultLookup.getBorder(this, ui, "List.focusSelectedCellHighlightBorder");
            }
            if (border == null) {
                border = DefaultLookup.getBorder(this, ui, "List.focusCellHighlightBorder");
            }
        } else {
        }

        return this;
    }
}