package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.rule.label.ITermLabelWorker;
import de.uka.ilkd.key.rule.label.SelectSkolemConstantTermLabelInstantiator;
import javax.swing.JMenu;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TermLabelMenu extends JMenu {

    public TermLabelMenu(final KeYMediator mediator) {
        
        this.setText("Term Labels");

        mediator.addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                removeAll();
                ImmutableList<ITermLabelWorker> termLabelWorkerList
                        = mediator.getSelectedProof().getSettings().getLabelSettings().getLabelInstantiators();
                for (ITermLabelWorker worker : termLabelWorkerList) {
                    for(ITermLabel termLabel: ((SelectSkolemConstantTermLabelInstantiator)worker).iTermLabelList){
                        add(termLabel.name().toString());
                    }
                }
            }
        });

    }

}
