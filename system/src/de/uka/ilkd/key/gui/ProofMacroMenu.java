// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
// 
package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ServiceLoader;
import javax.swing.*;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;

/**
 * This class provides the user interface to the macro extensions.
 *
 * <p>
 * It provides a menu with all macros which are applicable in a given context.
 * The check of of applicability is done using
 * {@link ProofMacro#canApplyTo(KeYMediator, PosInOccurrence)}.
 *
 * <p>
 * The menu items bear the name returned by {@link ProofMacro#getName()} and the
 * tooltip is set to {@link ProofMacro#getDescription()}.
 *
 * <p>
 * There are applicable macros iff {@link #isEmpty()} returns
 * <code>false</code>.
 *
 * <p>
 * The {@link ServiceLoader} mechanism is used to instantiate the registered
 * proof macros. To register a macro, add its class name to the file
 * <tt>resources/META-INF/services/de.uka.ilkd.key.macros.ProofMacro</tt>.
 *
 * @see ProofMacro
 * @see ServiceLoader
 *
 * @author mattias ulbrich
 */
public class ProofMacroMenu extends JMenu {


    private static final long serialVersionUID = -5946657022043894399L;

    /**
     * The loader used to access the providers for macros.
     */
    private static ServiceLoader<ProofMacro> loader = ServiceLoader.load(ProofMacro.class);

    /**
     * The number of defined macros.
     */
    private final int numberOfMacros;

    /**
     * Instantiates a new proof macro menu.
     *
     * Only applicable macros are added as menu items.
     *
     * @param mediator the mediator of the current proof.
     * @param posInOcc the pos in occurrence, can be <code>null</code> if not
     * available.
     */
    public ProofMacroMenu(KeYMediator mediator, PosInOccurrence posInOcc) {
        super("Strategy macros");

        int count = 0;
        for (ProofMacro macro : loader) {
            if (macro.canApplyTo(mediator, posInOcc)) {
                JMenuItem menuItem = createMenuItem(macro, mediator, posInOcc);
                add(menuItem);
                count++;
            }
        }

        mediator.enableWhenProofLoaded(this);
        this.numberOfMacros = count;
    }
    

    /**
     * Instantiates a new proof macro menu.
     * Only to be used in the {@link MainWindow}.
     *
     * Only macros applicable at any PosInOccurrence are added as menu items.
     *
     * @param mediator the mediator of the current proof.
     */
    ProofMacroMenu(KeYMediator mediator) {
        super("Strategy macros");

        int count = 0;
        for (ProofMacro macro : loader) {
            if (macro.isApplicableWithoutPosition()) {
                JMenuItem menuItem = createMenuItem(macro, mediator, null);
                add(menuItem);
                count++;
            }
        }

        mediator.enableWhenProofLoaded(this);
        this.numberOfMacros = count;
    }

    private JMenuItem createMenuItem(final ProofMacro macro,
            final KeYMediator mediator,
            final PosInOccurrence posInOcc) {

        JMenuItem menuItem = new JMenuItem(macro.getName());
        menuItem.setToolTipText(macro.getDescription());
        final KeyStroke macroKey = macro.getKeyStroke();
        if (macroKey != null && posInOcc == null) { // currently only for global macro applications
            menuItem.setAccelerator(macroKey);
        }
        menuItem.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (mediator.isInAutoMode()) return;
                final ProofMacroWorker worker = new ProofMacroWorker(macro, mediator, posInOcc);
                mediator.stopInterface(true);
                mediator.setInteractive(false);
                mediator.addInterruptedListener(worker);
                worker.execute();
            }
        });

        return menuItem;
    }

    /**
     * Checks if the menu is empty.
     *
     * @return <code>true</code>, if there are no applicable macros.
     */
    public boolean isEmpty() {
        return numberOfMacros == 0;
    }
}
