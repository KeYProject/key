package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.Markdown;
import de.uka.ilkd.key.gui.fonticons.FontAwesome;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
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
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class InteractionLogView extends JPanel implements InteractionRecorderListener {
    private static final float SMALL_ICON_SIZE = 16f;
    private final ExportProofScriptAction actionExportProofScript = new ExportProofScriptAction();
    private final SaveAction saveAction = new SaveAction();
    private final LoadAction loadAction = new LoadAction();
    private final AddUserNoteAction addUserNoteAction = new AddUserNoteAction();
    private final ToggleFavouriteAction toggleFavouriteAction = new ToggleFavouriteAction();
    private final JumpIntoTreeAction jumpIntoTreeAction = new JumpIntoTreeAction();
    private final TryReapplyAction tryReapplyAction = new TryReapplyAction();
    private final InteractionRecorder recoder = new InteractionRecorder();

    /**
     * the list of individual interactions (like impRight, auto, ...) in currently selected
     * interactionLog
     */
    private final JList<Interaction> listInteraction = new JList<>();
    /**
     * ComboBox for selecting a active InteractionLog
     */
    private final JComboBox<InteractionLog> interactionLogSelection = new JComboBox<>();
    /**
     * list of interactions, will be replaced on every change of the interactionLogSelection
     */
    private final DefaultListModel<Interaction> interactionListModel = new DefaultListModel<>();

    private final JToolBar panelButtons = new JToolBar();

    private final Services services;
    /**
     * contains a List of all opened InteractionLogs, which are selectable in the ComboBox
     */
    private final List<InteractionLog> loadedInteractionLogs = new ArrayList<InteractionLog>();
    private final JButton btnExport;
    private final JButton btnSave;
    private final JButton btnAddNote;
    private final JButton btnLoad;
    private Proof currentProof;
    /**
     * index of InteractionLog, that is written to in current proof.
     */
    private Optional<Integer> writingActionInteractionLog = Optional.empty();

    /**
     * currently displayed InteractionLog
     */
    private Optional<Integer> displayedInteractionLog = Optional.empty();

    public InteractionLogView(KeYMediator mediator) {
        services = mediator.getServices();
        listInteraction.setModel(interactionListModel);
        listInteraction.setCellRenderer(new InteractionCellRenderer());

        panelButtons.add(interactionLogSelection);
        panelButtons.add(btnLoad = new JButton(loadAction));
        panelButtons.add(btnSave = new JButton(saveAction));
        panelButtons.add(Box.createHorizontalGlue());

        panelButtons.add(btnExport = new JButton(actionExportProofScript));
        panelButtons.add(btnAddNote = new JButton(addUserNoteAction));

        btnExport.setHideActionText(true);
        btnSave.setHideActionText(true);
        btnAddNote.setHideActionText(true);
        btnLoad.setHideActionText(true);

        JPopupMenu popup = new JPopupMenu();
        popup.add(new JMenuItem(toggleFavouriteAction));
        popup.add(new JMenuItem(jumpIntoTreeAction));
        popup.add(new JMenuItem(tryReapplyAction));
        popup.addSeparator();
        popup.add(new JMenuItem(addUserNoteAction));
        listInteraction.setComponentPopupMenu(popup);


        recoder.addListener(this::onInteraction);

        interactionLogSelection.setModel(recoder.getLoadedInteractionLogs());
        interactionLogSelection.addActionListener(this::handleSelectionChange);
        interactionLogSelection.setModel(recoder.getLoadedInteractionLogs());

        listInteraction.addMouseMotionListener(new MouseMotionAdapter() {
            @Override
            public void mouseMoved(MouseEvent e) {
                JList l = (JList) e.getSource();
                ListModel m = l.getModel();
                int index = l.locationToIndex(e.getPoint());
                if (index > -1) {
                    Interaction inter = (Interaction) m.getElementAt(index);
                    l.setToolTipText("<html>" + Markdown.html(inter.getMarkdownText()) + "</html>");
                }
            }
        });


        interactionLogSelection.setModel(
                recoder.getLoadedInteractionLogs()
        );

        new DropTarget(listInteraction, 0, new DropTargetAdapter() {
            @Override
            public void drop(DropTargetDropEvent dtde) {
                Transferable tr = dtde.getTransferable();
                try {
                    Object textFlavour = tr.getTransferData(DataFlavor.stringFlavor);
                    dtde.acceptDrop(dtde.getDropAction());
                    dtde.dropComplete(true);
                    SwingUtilities.invokeLater(() -> {
                        addUserNoteAction.doAddNote(textFlavour.toString());
                    });
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
        recoder.addListener(this);

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
        recoder.get(currentProof);
        //rebuildList();
    }


    private void rebuildList() {
        InteractionLog currentInteractionLog = getSelectedItem();
        System.out.println(currentInteractionLog.getMarkdownText());
        if (currentProof != null) {
            InteractionLog state = recoder.get(currentProof);
            updateList(state);
        }
    }

    private void updateList(InteractionLog interactionLog) {
        interactionListModel.clear();
        interactionLog.getInteractions().forEach(interactionListModel::addElement);
    }

    /**
     * gets called on every change to the interaction
     *
     * @param interaction
     */
    @Override
    public void onInteraction(Interaction interaction) {
        rebuildList();
    }

    public ExportProofScriptAction getActionExportProofScript() {
        return actionExportProofScript;
    }

    public SaveAction getSaveAction() {
        return saveAction;
    }

    public LoadAction getLoadAction() {
        return loadAction;
    }

    public AddUserNoteAction getAddUserNoteAction() {
        return addUserNoteAction;
    }

    public JumpIntoTreeAction getJumpIntoTreeAction() {
        return jumpIntoTreeAction;
    }

    public TryReapplyAction getTryReapplyAction() {
        return tryReapplyAction;
    }

    public InteractionRecorder getRecoder() {
        return recoder;
    }

    private class InteractionLogModelItem extends DefaultComboBoxModel<InteractionLog> {
    }

    private class ExportProofScriptAction extends AbstractAction {
        public ExportProofScriptAction() {
            putValue(Action.NAME, "Export as KPS");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesomeBold.FILE_EXPORT, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            LogPrinter lp = new LogPrinter(services);
            InteractionLog state = recoder.get(currentProof);
            String ps = lp.print(state);
            System.out.println(ps);
        }
    }

    private class LoadAction extends AbstractAction {
        public LoadAction() {
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
                    recoder.readInteractionLog(file);
                    //addInteractionLog(importedLog);
                } catch (IOException exception) {
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
        public SaveAction() {
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
                } catch (IOException exception) {
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
        public AddUserNoteAction() {
            super("Add Note");
            putValue(Action.SMALL_ICON,
                    IconFontSwing.buildIcon(FontAwesome.STICKY_NOTE, SMALL_ICON_SIZE));
            //new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/book_add.png")));

        }

        @Override
        public void actionPerformed(ActionEvent e) {
            doAddNote("");
        }

        public void doAddNote(String prefilled) {
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
        public ToggleFavouriteAction() {
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
        public JumpIntoTreeAction() {
            super("Jump into tree");
            putValue(SMALL_ICON, IconFontSwing.buildIcon(FontAwesome.CODE, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {

        }
    }

    private class TryReapplyAction extends AbstractAction {
        public TryReapplyAction() {
            putValue(NAME, "Re-apply action");
            putValue(SMALL_ICON, IconFontSwing.buildIcon(FontAwesome.APPER, SMALL_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JOptionPane.showMessageDialog(null, "Not Implemented",
                    "A very expected error.", JOptionPane.ERROR_MESSAGE);
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