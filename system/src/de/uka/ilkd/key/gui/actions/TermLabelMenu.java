package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
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
                ImmutableList<String> termLabelNames
                        = mediator.getSelectedProof().env().getInitConfig().getProfile().getSupportedLabelNames();
                for (String name : termLabelNames) {
                    add(name);
                }
            }
        });

    }

}
