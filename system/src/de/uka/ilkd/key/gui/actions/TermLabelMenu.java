package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.logic.Name;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
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
                ImmutableList<Name> termLabelNames
                        = mediator.getSelectedProof().env().getInitConfig().getProfile().getSupportedLabelNames();
                List<String> stringNames = new LinkedList();
                for (Name name : termLabelNames) {
                    stringNames.add(name.toString());
                }
                Collections.sort(stringNames);
                for (String name : stringNames) {
                    add(name);
                }
            }
        });

    }

}
