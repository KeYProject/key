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
import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.KeyStroke;

import org.key_project.util.reflection.ClassLoaderUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.actions.ProofScriptFromFileAction;
import de.uka.ilkd.key.gui.actions.ProofScriptInputAction;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Node;

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
     *
     * This is used as iteration source in other parts of KeY's ui.
     */
    public static final Iterable<ProofMacro> REGISTERED_MACROS =
            ClassLoaderUtil.loadServices(ProofMacro.class);

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
        super("Strategy Macros");

        // Macros are group according to their category.
        // Store the submenus in this map.
        Map<String, JMenu> submenus = new HashMap<String, JMenu>();

        int count = 0;
        Node node = mediator.getSelectedNode();
        for (ProofMacro macro : REGISTERED_MACROS) {

            boolean applicable = node != null && macro.canApplyTo(node, posInOcc);

            if(applicable) {
                JMenuItem menuItem = createMenuItem(macro, mediator, posInOcc);

                String category = macro.getCategory();
                JMenu submenu = this;
                if(category != null) {
                    // find the submenu to be used. Create and store if necessary.
                    submenu = submenus.get(category);
                    if(submenu == null) {
                        submenu = new JMenu(category);
                        submenus.put(category, submenu);
                        add(submenu);
            }
        }

                submenu.add(menuItem);
                count++;
            }
        }

        if(Main.isExperimentalMode()) {
            add(new JMenuItem(new ProofScriptFromFileAction(mediator)));
            add(new JMenuItem(new ProofScriptInputAction(mediator)));
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
    public ProofMacroMenu(KeYMediator mediator) {
        this(mediator, null);
    }

    private JMenuItem createMenuItem(final ProofMacro macro,
            final KeYMediator mediator,
            final PosInOccurrence posInOcc) {

        JMenuItem menuItem = new JMenuItem(macro.getName());
        menuItem.setToolTipText(macro.getDescription());
        final KeyStroke macroKey = KeyStrokeManager.get(macro);

        if (macroKey != null && posInOcc == null) { // currently only for global macro applications
            menuItem.setAccelerator(macroKey);
        }
        menuItem.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (mediator.isInAutoMode()) {
                    return;
                }
                mediator.getUI().getProofControl().runMacro(mediator.getSelectedNode(), macro, posInOcc);
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
