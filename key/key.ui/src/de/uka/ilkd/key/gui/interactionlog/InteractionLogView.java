package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.script.*;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class InteractionLogView extends JPanel implements InteractionListeners {
    private final Action actionExportProofScript = new ExportProofScriptAction();
    private final Action saveAction = new SaveAction();
    private final Action loadAction = new LoadAction();

    private final JList<Interaction> listInteraction = new JList<>();
    private final JComboBox<Integer> interactionLogSelection = new JComboBox<>();
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
        panelButtons.add(new JButton(actionExportProofScript));
        panelButtons.add(new JButton(saveAction));

        if (loadedInteractionLogs.isEmpty()) {
            loadedInteractionLogs.add(new InteractionLog());
            setWritingActionInteractionLog(0);
            setDisplayedInteractionLog(0);
            System.out.println(getDisplayedInteractionLog());
        }


        panelButtons.add(new JButton(loadAction));
        panelButtons.add(interactionLogSelection);


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


    private void addInteractionLog(InteractionLog importedLog) {
        this.loadedInteractionLogs.add(importedLog);
        int index = this.loadedInteractionLogs.indexOf(importedLog);
        this.displayedInteractionLog = Optional.of(index);
        this.interactionLogSelection.addItem(index);
    }

    private void addInteractionsIoInteractionLog(List<NodeInteraction> nodeInteractions) {

        getWritingInteractionLog().ifPresent(interactionLog -> {
            List<Interaction> interactions = new ArrayList<>(nodeInteractions);
            interactionLog.setInteractions(interactions);
        });
    }

    private void setCurrentProof(Proof proof) {
        currentProof = proof;
        rebuildList();
    }

    private void rebuildList() {
        interactionListModel.clear();
        if (currentProof != null) {
            InteractionLog state = ScriptRecorderFacade.get(currentProof);
            getWritingInteractionLog().ifPresent(interactionLog -> {
                List<Interaction> interactions = new ArrayList<>();
                interactions.addAll(state.getInteractions());
                interactionLog.setInteractions(interactions);
            });
            state.getInteractions().forEach(interactionListModel::addElement);
        }
    }


    private Optional<InteractionLog> getWritingInteractionLog() {
        return writingActionInteractionLog.map(loadedInteractionLogs::get);
    }

    /**
     * change InteractionLog that should be written to
     *
     * @param index index of InteractionLog in getLoadedInteractionLogs()
     */
    public void setWritingActionInteractionLog(int index) {
        this.writingActionInteractionLog = Optional.of(index);
    }

    public List<InteractionLog> getLoadedInteractionLogs() {
        return this.loadedInteractionLogs;
    }

    @Override
    public void onInteraction(Interaction event) {
        if (event instanceof NodeInteraction) {
            //TODO if (((NodeInteraction) event).getNode().proof() == currentProof) {
            rebuildList();
            //}
        }
    }

    public Optional<InteractionLog> getDisplayedInteractionLog() {
        return displayedInteractionLog.map(loadedInteractionLogs::get);
    }

    private void setDisplayedInteractionLog(int i) {
        this.displayedInteractionLog = Optional.of(i);
    }

    private class ExportProofScriptAction extends AbstractAction {
        public ExportProofScriptAction() {
            putValue(Action.NAME, "Export as KPS");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            LogPrinter lp = new LogPrinter(services);
            InteractionLog state = ScriptRecorderFacade.get(currentProof);
            String ps = lp.print(state);
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
                    InteractionLog importedLog = InteractionLogFacade.readInteractionLog(file);
                    addInteractionLog(importedLog);
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
                getDisplayedInteractionLog().ifPresent((displayedInteractionLog) -> {
                    try {
                        InteractionLogFacade.storeInteractionLog(displayedInteractionLog, fileChooser.getSelectedFile());
                    } catch (IOException exception) {
                        JOptionPane.showMessageDialog(null,
                                exception.getCause(),
                                "IOException",
                                JOptionPane.WARNING_MESSAGE);
                        exception.printStackTrace();
                    }
                });
            }
        }
    }
}

class InteractionCellRenderer extends DefaultListCellRenderer {
    private final Services services;

    InteractionCellRenderer(Services services) {
        this.services = services;
    }

    @Override
    public Component getListCellRendererComponent(JList<?> list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
        JLabel lbl = (JLabel) super.getListCellRendererComponent(list, value, index, isSelected, cellHasFocus);
        lbl.setText(
                String.format("<html><pre>", index) +
                        ((NodeInteraction) value).getProofScriptRepresentation(services) + "</pre></html>");
        return lbl;
    }
}