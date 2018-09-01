package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.script.*;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;

public class InteractionLogView extends JPanel implements InteractionListeners {
    private final Action actionExportProofScript = new ExportProofScriptAction();
    private final JList<Interaction> listInteraction = new JList<>();
    private final DefaultListModel<Interaction> interactionListModel = new DefaultListModel<>();
    private final Box panelButtons = new Box(BoxLayout.Y_AXIS);
    private final Services services;
    private Proof currentProof;

    public InteractionLogView(KeYMediator mediator) {
        services = mediator.getServices();
        listInteraction.setModel(interactionListModel);
        listInteraction.setCellRenderer(new InteractionCellRenderer(mediator.getServices()));

        panelButtons.add(Box.createHorizontalGlue());
        panelButtons.add(new JButton(actionExportProofScript));

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


    private void setCurrentProof(Proof proof) {
        currentProof = proof;
        rebuildList();
    }

    private void rebuildList() {
        interactionListModel.clear();
        if (currentProof != null) {
            ScriptRecorderState state = ScriptRecorderFacade.get(currentProof);
            state.getInteractions().forEach(interactionListModel::addElement);
        }
    }

    @Override
    public void onInteraction(Interaction event) {
        if (event.getNode().proof() == currentProof) {
            rebuildList();
        }
    }

    private class ExportProofScriptAction extends AbstractAction {
        public ExportProofScriptAction() {
            putValue(Action.NAME, "Export as KPS");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            LogPrinter lp = new LogPrinter(services);
            ScriptRecorderState state = ScriptRecorderFacade.get(currentProof);
            String ps = lp.print(state);
            System.out.println(ps);
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
                        ((Interaction) value).getProofScriptRepresentation(services) + "</pre></html>");
        return lbl;
    }
}