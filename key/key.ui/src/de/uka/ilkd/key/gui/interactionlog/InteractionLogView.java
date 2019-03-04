package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesome;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.interactionlog.algo.MUProofScriptExport;
import de.uka.ilkd.key.gui.interactionlog.algo.MarkdownExport;
import de.uka.ilkd.key.gui.interactionlog.algo.Reapplication;
import de.uka.ilkd.key.gui.interactionlog.model.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.datatransfer.*;
import java.awt.dnd.DropTarget;
import java.awt.dnd.DropTargetAdapter;
import java.awt.dnd.DropTargetDropEvent;
import java.awt.event.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Optional;

public class InteractionLogView extends JPanel implements InteractionRecorderListener {
    private static final float SMALL_ICON_SIZE = 16f;
    private static final String MENU_ILOG = "Interaction Logging";
    private static final String MENU_ILOG_EXPORT = MENU_ILOG + ".Export";
    private final InteractionRecorder recorder = new InteractionRecorder();

    private final ExportMUScriptAction actionExportProofScript = new ExportMUScriptAction();
    private final ExportKPSAction actionKPSExport = new ExportKPSAction();
    private final SaveAction actionSave = new SaveAction();
    private final LoadAction actionLoad = new LoadAction();
    private final AddUserNoteAction actionAddUserNote = new AddUserNoteAction();
    private final ToggleFavouriteAction actionToggleFavourite = new ToggleFavouriteAction();
    private final JumpIntoTreeAction actionJumpIntoTree = new JumpIntoTreeAction();
    private final TryReapplyAction actionTryReapply = new TryReapplyAction();
    private final ExportMarkdownAction actionExportMarkdown = new ExportMarkdownAction();
    private final ShowExtendedActionsAction actionShowExtended = new ShowExtendedActionsAction();
    private final ExportMUScriptClipboardAction actionMUCopyClipboard = new ExportMUScriptClipboardAction();
    private final PauseLoggingAction actionPauseLogging = new PauseLoggingAction();


    private final JList<Interaction> listInteraction = new JList<>();
    private final JComboBox<InteractionLog> interactionLogSelection = new JComboBox<>();
    private final DefaultListModel<Interaction> interactionListModel = new DefaultListModel<>();
    private KeYMediator mediator;
    private Proof currentProof;
    private final KeYSelectionListener keYSelectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            setCurrentProof(e.getSource().getSelectedProof());
        }
    };
    private JFileChooser fileChooser;

    public InteractionLogView() {
        // register the recorder in the proof control
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
        popup.add(new JMenuItem(actionMUCopyClipboard));
        popup.addSeparator();
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

    private JFileChooser getFileChooser() {
        if (fileChooser == null) {
            fileChooser = new JFileChooser();
            if (currentProof != null) {
                File file = currentProof.getProofFile();
                if (file != null)
                    fileChooser.setCurrentDirectory(file.getParentFile());
            }
        }
        return fileChooser;
    }

    @Override
    public void onInteraction(Interaction interaction) {
        rebuildList();
    }

    public ExportMUScriptAction getActionExportProofScript() {
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

    public void setMediator(KeYMediator mediator) {
        if (this.mediator != null) {
            this.mediator.removeKeYSelectionListener(keYSelectionListener);
        }
        this.mediator = mediator;
        mediator.addKeYSelectionListener(keYSelectionListener);
        setCurrentProof(mediator.getSelectedProof());
    }

    public void setMainWindow(MainWindow window) {
        window.getUserInterface().getProofControl().addInteractionListener(recorder);
        window.getUserInterface().getProofControl().addAutoModeListener(recorder);
    }

    public ExportKPSAction getActionKPSExport() {
        return actionKPSExport;
    }

    public ToggleFavouriteAction getActionToggleFavourite() {
        return actionToggleFavourite;
    }

    public ExportMarkdownAction getActionExportMarkdown() {
        return actionExportMarkdown;
    }

    public ShowExtendedActionsAction getActionShowExtended() {
        return actionShowExtended;
    }

    public ExportMUScriptClipboardAction getActionMUCopyClipboard() {
        return actionMUCopyClipboard;
    }

    public PauseLoggingAction getActionPauseLogging() {
        return actionPauseLogging;
    }

    public JList<Interaction> getListInteraction() {
        return listInteraction;
    }

    public JComboBox<InteractionLog> getInteractionLogSelection() {
        return interactionLogSelection;
    }

    public DefaultListModel<Interaction> getInteractionListModel() {
        return interactionListModel;
    }

    private class InteractionLogModelItem extends DefaultComboBoxModel<InteractionLog> {
    }

    private class ExportMUScriptAction extends AbstractFileSaveAction {
        ExportMUScriptAction() {
            putValue(Action.NAME, "Export as Proof Script");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.FILE_EXPORT, SMALL_ICON_SIZE));

            setMenuPath(MENU_ILOG_EXPORT);
        }

        @Override
        void save(File selectedFile) {
            InteractionLog current = getSelectedItem();
            String script = MUProofScriptExport.getScript(current);
            try (FileWriter fw = new FileWriter(selectedFile)) {
                fw.write(script);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private class ExportMUScriptClipboardAction extends KeyAction {
        ExportMUScriptClipboardAction() {
            putValue(Action.NAME, "Copy MUScript");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.COPY, SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG_EXPORT);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            String text = MUProofScriptExport.getScriptRepresentation(listInteraction.getSelectedValue());
            Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
            StringSelection contents = new StringSelection(text);
            clipboard.setContents(contents, contents);
        }
    }

    private class LoadAction extends KeyAction {
        LoadAction() {
            putValue(Action.NAME, "Load");
            putValue(Action.SHORT_DESCRIPTION, "Load Interaction Log");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.TRUCK_LOADING, SMALL_ICON_SIZE));
            // new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_add.png")));
            setPriority(0);
            setMenuPath(MENU_ILOG);
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

    private class SaveAction extends KeyAction {
        SaveAction() {
            putValue(Action.NAME, "Save");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesome.SAVE, SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG);
            setPriority(1);
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_save.png")));
        }


        @Override
        public void actionPerformed(ActionEvent e) {
            JFileChooser fileChooser = getFileChooser();
            int returnValue = fileChooser.showSaveDialog(null);
            if (returnValue == JFileChooser.APPROVE_OPTION) {
                InteractionLog activeInteractionLog = getSelectedItem();
                try {
                    InteractionLogFacade.storeInteractionLog(activeInteractionLog,
                            fileChooser.getSelectedFile());
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

    private class AddUserNoteAction extends KeyAction {
        AddUserNoteAction() {
            setName("Add Note");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesome.STICKY_NOTE, SMALL_ICON_SIZE));
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/book_add.png")));
            setMenuPath(MENU_ILOG);
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

    private class ToggleFavouriteAction extends KeyAction {
        ToggleFavouriteAction() {
            setName("Toggle Fav");
            setName("Toggle Fav");
            putValue(Action.MNEMONIC_KEY, KeyEvent.VK_F);
            putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_M, InputEvent.CTRL_MASK));
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.HEART, SMALL_ICON_SIZE, Color.red));
            //    new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/heart.png")));
            setMenuPath(MENU_ILOG);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (listInteraction.getSelectedValue() != null) {
                listInteraction.getSelectedValue().setFavoured(!listInteraction.getSelectedValue().isFavoured());
            }
        }
    }

    private class JumpIntoTreeAction extends KeyAction {
        JumpIntoTreeAction() {
            setName("Jump into tree");
            putValue(SMALL_ICON, IconFontSwing.buildIcon(FontAwesome.CODE, SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                NodeInteraction current = (NodeInteraction) listInteraction.getSelectedValue();
                if (current != null) {
                    Node node = current.getNode(mediator.getSelectedProof());
                    mediator.getSelectionModel().setSelectedNode(node);
                }
            } catch (ClassCastException ex) {

            }
        }
    }

    private class TryReapplyAction extends KeyAction {
        TryReapplyAction() {
            putValue(NAME, "Re-apply action");
            putValue(SMALL_ICON, IconFontSwing.buildIcon(FontAwesome.APPER, SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Interaction inter = listInteraction.getSelectedValue();
            try {
                //Reapplication should be ignored by the logging.
                recorder.setDisableAll(true);
                Reapplication reapplication = new Reapplication(mediator.getSelectedGoal());
                if (inter != null) inter.accept(reapplication);
            } catch (UnsupportedOperationException ex) {
                JOptionPane.showMessageDialog(null,
                        String.format("<html>Reapplication of %s is not implemented<br>If you know how to do it, then override the corresponding method in %s.</html>",
                                inter.getClass(), Reapplication.class),
                        "A very expected error.", JOptionPane.ERROR_MESSAGE);
            } catch (IllegalStateException ex) {

            } finally {
                recorder.setDisableAll(false);
            }
        }
    }

    private abstract class AbstractFileSaveAction extends KeyAction {
        public AbstractFileSaveAction() {
            super();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JFileChooser fc = getFileChooser();
            int choice = fc.showSaveDialog((Component) e.getSource());
            if (choice == JFileChooser.APPROVE_OPTION) {
                save(fc.getSelectedFile());
            }
        }

        abstract void save(File selectedFile);
    }

    private class ExportKPSAction extends AbstractFileSaveAction {
        public ExportKPSAction() {
            setName("Export as KPS …");
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into the KPS format.");
            putValue(Action.SMALL_ICON, IconFontSwing.buildIcon(FontAwesomeBold.CODE, SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG_EXPORT);
        }

        void save(File selectedFile) {
            try (FileWriter fw = new FileWriter(selectedFile)) {
                MarkdownExport.writeTo(getSelectedItem(), new PrintWriter(fw));
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private class ExportMarkdownAction extends AbstractFileSaveAction {
        public ExportMarkdownAction() {
            setName("Export as markdown …");
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into a markdown file.");
            putValue(Action.SMALL_ICON, IconFontSwing.buildIcon(FontAwesomeBold.MARKDOWN, SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG_EXPORT);
        }

        void save(File selectedFile) {
            try (FileWriter fw = new FileWriter(selectedFile)) {
                MarkdownExport.writeTo(getSelectedItem(), new PrintWriter(fw));
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private class ShowExtendedActionsAction extends KeyAction {
        public ShowExtendedActionsAction() {
            setName("More …");
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
            menu.show(btn, 0, 0);
            //pi.getLocation().x, pi.getLocation().y);
        }
    }

    private class PauseLoggingAction extends KeyAction {
        public PauseLoggingAction() {
            setSelected(recorder.isDisableAll());
            setPriority(-1);
            setMenuPath(MENU_ILOG);
            putValue(Action.SHORT_DESCRIPTION, "Activation or Deactivation of interaction logging");

            update();
            addPropertyChangeListener(evt -> {
                if (evt.getPropertyName().equals(SELECTED_KEY))
                    update();
            });
        }

        private void update() {
            if (!isSelected()) {
                setIcon(IconFontSwing.buildIcon(FontAwesomeBold.PAUSE_CIRCLE, SMALL_ICON_SIZE));
                setName("Pause Interaction Logging");
            } else {
                setIcon(IconFontSwing.buildIcon(FontAwesomeBold.PLAY_CIRCLE, SMALL_ICON_SIZE));
                setName("Resume Interaction Logging");
            }
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setSelected(!isSelected());
            recorder.setDisableAll(isSelected());
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
                border = UIManager.getDefaults().getBorder("List.focusSelectedCellHighlightBorder");
            }
            if (border == null) {
                border = UIManager.getDefaults().getBorder("List.focusCellHighlightBorder");
            }
        } else {
        }

        return this;
    }


}