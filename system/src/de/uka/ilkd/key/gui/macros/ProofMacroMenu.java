package de.uka.ilkd.key.gui.macros;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ServiceLoader;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;

@SuppressWarnings("serial")
public class ProofMacroMenu extends JMenu {

    private static ServiceLoader<ProofMacro> loader = ServiceLoader.load(ProofMacro.class);

    private final int numberOfMacros;

    public ProofMacroMenu(KeYMediator mediator, PosInOccurrence posInOcc) {
        super("Strategy macros");

        int count = 0;
        for (ProofMacro macro : loader) {
            if(macro.canApplyTo(mediator, posInOcc)) {
                JMenuItem menuItem = createMenuItem(macro, mediator, posInOcc);
                add(menuItem);
                count ++;
            }
        }

        this.numberOfMacros = count;
    }

    private JMenuItem createMenuItem(final ProofMacro macro, 
            final KeYMediator mediator,
            final PosInOccurrence posInOcc) {

        JMenuItem menuItem = new JMenuItem(macro.getName());
        menuItem.setToolTipText(macro.getDescription());
        menuItem.addActionListener(new ActionListener() {
            @Override 
            public void actionPerformed(ActionEvent e) {
                macro.applyTo(mediator, posInOcc);
            }
        });

        return menuItem;
    }


    public boolean isEmpty() {
        return numberOfMacros == 0;
    }

}
