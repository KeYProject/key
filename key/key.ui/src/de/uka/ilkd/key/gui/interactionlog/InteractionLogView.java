package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.script.*;

import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.script.Interaction;
import de.uka.ilkd.key.util.script.InteractionListeners;
import de.uka.ilkd.key.util.script.InteractionLog;
import de.uka.ilkd.key.util.script.InteractionLogFacade;
import de.uka.ilkd.key.util.script.LogPrinter;
import de.uka.ilkd.key.util.script.NodeInteraction;
import de.uka.ilkd.key.util.script.ScriptRecorderFacade;
import sun.font.Script;

public class InteractionLogView extends JPanel implements InteractionListeners {
    private final Action actionExportProofScript = new ExportProofScriptAction();
    private final Action saveAction = new SaveAction();
    private final Action loadAction = new LoadAction();
    private final Action addUserNoteAction = new AddUserNoteAction();

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
    //private final Box panelButtons = new Box(BoxLayout.X_AXIS);
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
        listInteraction.setCellRenderer(new InteractionCellRenderer(mediator.getServices()));

        panelButtons.add(Box.createHorizontalGlue());
        panelButtons.add(btnExport = new JButton(actionExportProofScript));
        panelButtons.add(btnSave = new JButton(saveAction));
        panelButtons.add(btnAddNote = new JButton(addUserNoteAction));
        panelButtons.add(btnLoad = new JButton(loadAction));

        btnExport.setHideActionText(true);
        btnSave.setHideActionText(true);
        btnAddNote.setHideActionText(true);
        btnLoad.setHideActionText(true);

        JPopupMenu popup = new JPopupMenu();
        JMenuItem favouriteButton = new JMenuItem("toggle favourites");
        favouriteButton.setIcon(new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/heart.png")));
        favouriteButton.addActionListener(actionEvent -> {
          listInteraction.getSelectedValue().setFavoured(!listInteraction.getSelectedValue().isFavoured());
        });
        popup.add(favouriteButton);
        listInteraction.setComponentPopupMenu(popup);


        ScriptRecorderFacade.addListener(this::onInteraction);

        interactionLogSelection.setRenderer(new DefaultListCellRenderer() {
            @Override
            public Component getListCellRendererComponent(JList<?> jList, Object o, int i, boolean b, boolean b1) {
                String name = "-";
                if (o != null) {
                    name = o.toString();
                }

                return super.getListCellRendererComponent(jList, name, i, b, b1);
            }
        });

        interactionLogSelection.setModel(ScriptRecorderFacade.getLoadedInteractionLogs());
        interactionLogSelection.addActionListener(this::handleSelectionChange);

        interactionLogSelection.setModel(ScriptRecorderFacade.getLoadedInteractionLogs());
        panelButtons.add(interactionLogSelection);

        interactionLogSelection.setModel(
                ScriptRecorderFacade.getLoadedInteractionLogs()
        );

        setLayout(new BorderLayout());
        add(panelButtons, BorderLayout.NORTH);
        add(new JScrollPane(listInteraction));
        ScriptRecorderFacade.addListener(this);

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
        ScriptRecorderFacade.get(currentProof);
        //rebuildList();
    }


    private void rebuildList() {
        InteractionLog currentInteractionLog = getSelectedItem();
        if (currentProof != null) {
            InteractionLog state = ScriptRecorderFacade.get(currentProof);
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

    private class InteractionLogModelItem extends DefaultComboBoxModel<InteractionLog> {
    }

    private class ExportProofScriptAction extends AbstractAction {
        public ExportProofScriptAction() {
            putValue(Action.NAME, "Export as KPS");
            putValue(Action.SMALL_ICON,
                    new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_add.png")));

        }

        @Override
        public void actionPerformed(ActionEvent e) {
            LogPrinter lp = new LogPrinter(services);
            InteractionLog state = ScriptRecorderFacade.get(currentProof);
            String ps = lp.print(state);
            System.out.println(ps);
        }
    }

    private class LoadAction extends AbstractAction {
        public LoadAction() {
            putValue(Action.NAME, "Load Interaction Log");
            putValue(Action.SMALL_ICON,
                    new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_add.png")));
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
                    ScriptRecorderFacade.readInteractionLog(file);
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
                    new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/database_save.png")));
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
                    new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/book_add.png")));

        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Optional<String> note = MultiLineInputPrompt.show(InteractionLogView.this, "Enter note...");
            if (note.isPresent()) {
                UserNoteInteraction interaction = new UserNoteInteraction(note.get());
                InteractionLog interactionLog = (InteractionLog) interactionLogSelection.getSelectedItem();
                if (interactionLog.getInteractions() != null)
                    interactionLog.getInteractions().add(interaction);
                onInteraction(interaction);
            }
        }
    }
}

class MultiLineInputPrompt {
    public static Optional<String> show(JComponent parent, String title) {
        JPanel panel = new JPanel(new BorderLayout());
        JTextArea area = new JTextArea();
        panel.add(new JScrollPane(area));
        int c = JOptionPane.showConfirmDialog(parent, panel, "Enter note...", JOptionPane.OK_CANCEL_OPTION);
        if (c == JOptionPane.OK_OPTION) {
            return Optional.of(area.getText());
        } else return Optional.empty();
    }
}

class InteractionCellRenderer extends DefaultListCellRenderer {
    private final Services services;
    private final DateFormat df = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");


    InteractionCellRenderer(Services services) {
        this.services = services;
    }


    @Override
    public Component getListCellRendererComponent(JList<?> list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
        JLabel lbl = (JLabel) super.getListCellRendererComponent(list, value, index, isSelected, cellHasFocus);
        Interaction inter = (Interaction) value;
        lbl.setText(df.format(inter.getCreated()) + " " + inter);
        if (inter.isFavoured()) {
            lbl.setIcon(new ImageIcon(getClass().getResource("/de/uka/ilkd/key/gui/icons/heart.png")));
            lbl.setBackground(new Color(0xFFD373));
        } else {
            lbl.setBackground(SystemColor.WHITE);
        }
        return lbl;
    }
}