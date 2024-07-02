package org.key_project.ui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.ui.BoundsPopupMenuListener;
import org.key_project.ui.interactionlog.algo.MUProofScriptExport;
import org.key_project.ui.interactionlog.algo.MarkdownExport;
import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.ui.interactionlog.model.InteractionLog;
import org.key_project.ui.interactionlog.model.InteractionRecorderListener;
import org.key_project.ui.interactionlog.model.NodeInteraction;
import org.key_project.ui.interactionlog.model.UserNoteInteraction;

import javax.swing.*;
import javax.swing.border.Border;
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

public class InteractionLogView extends JPanel implements InteractionRecorderListener, TabPanel {
    private static final long serialVersionUID = -7022558787824644419L;
    private static final Icon INTERACTION_LOG_ICON = IconFactory.INTERLOG_ICON.get();
    private static final float SMALL_ICON_SIZE = 16f;
    private static final String MENU_ILOG = "Interaction Logging";
    private static final String MENU_ILOG_EXPORT = MENU_ILOG + ".Export";

    private static final IconFontProvider ICON_LOAD =
            new IconFontProvider(FontAwesomeSolid.TRUCK_LOADING);
    private static final IconFontProvider ICON_ADD_USER_ACTION =
            new IconFontProvider(FontAwesomeRegular.STICKY_NOTE);
    private static final IconFontProvider ICON_TOGGLE_FAVOURITE =
            new IconFontProvider(FontAwesomeSolid.HEART);


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
    private final ExportMUScriptClipboardAction actionMUCopyClipboard =
            new ExportMUScriptClipboardAction();
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

    public InteractionLogView(MainWindow window, KeYMediator mediator) {
        // register the recorder in the proof control
        listInteraction.setModel(interactionListModel);
        listInteraction.setCellRenderer(new InteractionCellRenderer());

        BoundsPopupMenuListener listener =
                new BoundsPopupMenuListener(true, false);
        interactionLogSelection.addPopupMenuListener(listener);
        interactionLogSelection.setPrototypeDisplayValue(
                new InteractionLog("INTERACTION LOG"));


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

        setMainWindow(window);
        setMediator(mediator);
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


    @Override
    public String getTitle() {
        return "Interaction Log";
    }

    @Override
    public Icon getIcon() {
        return INTERACTION_LOG_ICON;
    }

    @Override
    public JComponent getComponent() {
        return this;
    }


    private class InteractionLogModelItem extends DefaultComboBoxModel<InteractionLog> {
        private static final long serialVersionUID = -865181384700785594L;
    }

    private class ExportMUScriptAction extends AbstractFileSaveAction {
        private static final long serialVersionUID = -1452819623911938236L;

        ExportMUScriptAction() {
            setName("Export as Proof Script...");
            setIcon(IconFactory.EXPORT_MU_SCRIPT.get());
            setMenuPath(MENU_ILOG_EXPORT);
            setPriority(2);
            lookupAcceleratorKey();
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
        private static final long serialVersionUID = 3061052373321132190L;

        ExportMUScriptClipboardAction() {
            setName("Copy MUScript");
            setSmallIcon(IconFactory.EXPORT_MU_SCRIPT_CLIPBOARD.get());
            setMenuPath(MENU_ILOG_EXPORT);
            setPriority(5);
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Interaction selectedValue = listInteraction.getSelectedValue();
            if (selectedValue != null) {
                String text = selectedValue.getProofScriptRepresentation();
                GuiUtilities.setClipboardText(text);
            }
        }
    }

    private class LoadAction extends KeyAction {
        private static final long serialVersionUID = 7081382326391914209L;

        LoadAction() {
            setName("Load...");
            putValue(Action.SHORT_DESCRIPTION, "Load Interaction Log");
            setIcon(ICON_LOAD.get(SMALL_ICON_SIZE));
            setPriority(0);
            setMenuPath(MENU_ILOG);
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            KeYFileChooser fc = KeYFileChooser.getFileChooser("Load interaction log");
            fc.setFileFilter(KeYFileChooser.INTERACTION_LOG_FILTER);

            if (fc.showOpenDialog(InteractionLogView.this) == JFileChooser.APPROVE_OPTION) {
                try {
                    File file = fc.getSelectedFile();
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
        private static final long serialVersionUID = 152427005520690908L;


        SaveAction() {
            setName("Save...");
            setIcon(IconFactory.INTERLOG_SAVE.get());
            setMenuPath(MENU_ILOG);
            setPriority(1);
            lookupAcceleratorKey();
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_save.png")));
        }


        @Override
        public void actionPerformed(ActionEvent e) {
            KeYFileChooser fc = KeYFileChooser.getFileChooser("Save file");
            fc.setFileFilter(KeYFileChooser.INTERACTION_LOG_FILTER);
            if (fc.showSaveDialog(InteractionLogView.this) == JFileChooser.APPROVE_OPTION) {
                InteractionLog activeInteractionLog = getSelectedItem();
                try {
                    InteractionLogFacade.storeInteractionLog(activeInteractionLog,
                            fc.getSelectedFile());
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
        private static final long serialVersionUID = -4194158336899285273L;

        AddUserNoteAction() {
            setName("Add Note...");
            setIcon(ICON_ADD_USER_ACTION.get(SMALL_ICON_SIZE));
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/book_add.png")));
            setMenuPath(MENU_ILOG);
            setPriority(9);
            lookupAcceleratorKey();
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
        private static final long serialVersionUID = -8405580442311567192L;

        ToggleFavouriteAction() {
            setName("Toggle Favourite");
            putValue(Action.MNEMONIC_KEY, KeyEvent.VK_F);
            putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_M, InputEvent.CTRL_MASK));
            setIcon(ICON_TOGGLE_FAVOURITE.get(SMALL_ICON_SIZE));
            setMenuPath(MENU_ILOG);
            setPriority(8);
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (listInteraction.getSelectedValue() != null) {
                listInteraction.getSelectedValue().setFavoured(!listInteraction.getSelectedValue().isFavoured());
            }
        }
    }

    private class JumpIntoTreeAction extends KeyAction {
        private static final long serialVersionUID = -2750634259700985279L;

        JumpIntoTreeAction() {
            setName("Jump into Tree");
            putValue(SMALL_ICON, IconFactory.JUMP_INTO_TREE.get());
            setMenuPath(MENU_ILOG);
            setPriority(6);
            lookupAcceleratorKey();
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
        private static final long serialVersionUID = -5660321248967150793L;

        TryReapplyAction() {
            putValue(NAME, "Reapply Action");
            putValue(SMALL_ICON, IconFactory.INTERLOG_TRY_APPLY.get());
            setMenuPath(MENU_ILOG);
            setPriority(7);
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Interaction inter = listInteraction.getSelectedValue();
            try {
                //Reapplication should be ignored by the logging.
                recorder.setDisableAll(true);
                inter.reapply(/*TODO*/ null, mediator.getSelectedGoal());
            } catch (UnsupportedOperationException ex) {
                JOptionPane.showMessageDialog(null,
                        String.format("<html>Reapplication of %s is not implemented<br>If you know how to do it, then override the corresponding method in %s.</html>",
                                inter.getClass()), "A very expected error.", JOptionPane.ERROR_MESSAGE);
            } catch (Exception e1) {
                e1.printStackTrace();
            } finally {
                recorder.setDisableAll(false);
            }
        }
    }

    private abstract class AbstractFileSaveAction extends KeyAction {
        private static final long serialVersionUID = -5654233544157162006L;

        public AbstractFileSaveAction() {
            super();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            KeYFileChooser fc = KeYFileChooser.getFileChooser("Save File");
            fc.setFileFilter(KeYFileChooser.INTERACTION_LOG_FILTER);
            if (fc.showSaveDialog(InteractionLogView.this) == JFileChooser.APPROVE_OPTION) {
                save(fc.getSelectedFile());
            }
        }

        abstract void save(File selectedFile);
    }

    private class ExportKPSAction extends AbstractFileSaveAction {
        private static final long serialVersionUID = -5601133423736836904L;

        public ExportKPSAction() {
            setName("Export as KPS...");
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into the KPS format.");
            setIcon(IconFactory.INTERLOG_EXPORT_KPS.get());
            setMenuPath(MENU_ILOG_EXPORT);
            setPriority(3);
            lookupAcceleratorKey();
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
        private static final long serialVersionUID = 1108419704071886953L;

        public ExportMarkdownAction() {
            setName("Export as Markdown...");
            putValue(Action.SHORT_DESCRIPTION, "Export the current log into a markdown file.");
            setIcon(IconFactory.INTERLOG_EXPORT_MARKDOWN.get());
            setMenuPath(MENU_ILOG_EXPORT);
            setPriority(4);
            lookupAcceleratorKey();
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
        private static final long serialVersionUID = -2526178400655285314L;

        public ShowExtendedActionsAction() {
            setName("More...");
            putValue(Action.SHORT_DESCRIPTION, "Shows further options");
            setIcon(IconFactory.INTERLOW_EXTENDED_ACTIONS.get());
            lookupAcceleratorKey();
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
        private static final long serialVersionUID = 714043827891022783L;

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
            lookupAcceleratorKey();
        }

        private void update() {
            if (!isSelected()) {
                setIcon(IconFactory.INTERLOG_PAUSE.get());
                setName("Pause Interaction Logging");
            } else {
                setIcon(IconFactory.INTERLOG_RESUME.get());
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
            dialog.setTitle("Enter note");

            JPanel root = new JPanel(new BorderLayout(10, 10));
            JPanel box = new JPanel(new FlowLayout(FlowLayout.CENTER));
            root.add(box, BorderLayout.SOUTH);
            JTextArea area = new JTextArea(text);
            JButton okButton = new JButton("OK");
            JButton cancelButton = new JButton("Cancel");
            box.add(okButton);
            box.add(cancelButton);

            okButton.addActionListener(evt -> accept(area.getText()));
            cancelButton.addActionListener(evt -> cancel());
            dialog.setDefaultCloseOperation(WindowConstants.HIDE_ON_CLOSE);
            dialog.addWindowListener(new WindowAdapter() {
                @Override
                public void windowClosed(WindowEvent e) {
                    cancel();
                }
            });
            dialog.setContentPane(root);

            root.add(new JScrollPane(area), BorderLayout.CENTER);

            dialog.setSize(300, 200);
            // center over main window if the parent is currently hidden (e.g., inside a tabbedPane)
            if (parent == null || !parent.isShowing()) {
                dialog.setLocationRelativeTo(MainWindow.getInstance());
            } else {
                dialog.setLocationRelativeTo(parent);
            }

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
    private static final long serialVersionUID = -2667005473245735632L;
    private static final DateFormat df = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
    private static final Color COLOR_FAVOURED = new Color(0xFFD373);
    private JLabel lblIconLeft = new JLabel(), lblIconRight = new JLabel(), lblText = new JLabel();
    private Icon iconHeart = IconFactory.INTERLOG_TOGGLE_FAV.get();

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
