/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.actions.ProofScriptFromFileAction;
import de.uka.ilkd.key.gui.actions.ProofScriptInputAction;
import de.uka.ilkd.key.gui.actions.useractions.ProofMacroUserAction;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Node;

import org.key_project.util.reflection.ClassLoaderUtil;

/**
 * This class provides the user interface to the macro extensions.
 *
 * <p>
 * It provides a menu with all macros which are applicable in a given context. The check of of
 * applicability is done using {@link ProofMacro#canApplyTo(KeYMediator, PosInOccurrence)}.
 *
 * <p>
 * The menu items bear the name returned by {@link ProofMacro#getName()} and the tooltip is set to
 * {@link ProofMacro#getDescription()}.
 *
 * <p>
 * There are applicable macros iff {@link #isEmpty()} returns <code>false</code>.
 *
 * <p>
 * The {@link ServiceLoader} mechanism is used to instantiate the registered proof macros. To
 * register a macro, add its class name to the file
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
     * @param posInOcc the pos in occurrence, can be <code>null</code> if not available.
     */
    public ProofMacroMenu(KeYMediator mediator, PosInOccurrence posInOcc) {
        super("Strategy Macros");

        // Macros are grouped according to their category.
        Map<String, List<JMenuItem>> submenus = new LinkedHashMap<>();

        int count = 0;
        Node node = mediator.getSelectedNode();
        for (ProofMacro macro : REGISTERED_MACROS) {
            boolean applicable = node != null && macro.canApplyTo(node, posInOcc);

            if (applicable) {
                JMenuItem menuItem = createMenuItem(macro, mediator, posInOcc);
                String category = macro.getCategory();
                submenus.computeIfAbsent(category, x -> new ArrayList<>()).add(menuItem);
                count++;
            }
        }

        boolean first = true;
        for (Map.Entry<String, List<JMenuItem>> entry : submenus.entrySet()) {
            List<JMenuItem> items = entry.getValue();
            if (first) {
                first = false;
            } else {
                addSeparator();
            }

            for (JMenuItem item : items) {
                add(item);
            }
        }

        if (Main.isExperimentalMode()) {
            addSeparator();
            add(new JMenuItem(new ProofScriptFromFileAction(mediator)));
            add(new JMenuItem(new ProofScriptInputAction(mediator)));
        }

        mediator.enableWhenProofLoaded(this);
        this.numberOfMacros = count;
    }

    private static JMenuItem createMenuItem(final ProofMacro macro, final KeYMediator mediator,
            final PosInOccurrence posInOcc) {

        JMenuItem menuItem = new JMenuItem(macro.getName());
        menuItem.setToolTipText(macro.getDescription());
        final KeyStroke macroKey = KeyStrokeManager.get(macro);

        if (macroKey != null && posInOcc == null) { // currently only for global macro applications
            menuItem.setAccelerator(macroKey);
        }

        menuItem.addActionListener(
            new ProofMacroUserAction(mediator, macro, posInOcc, mediator.getSelectedProof()));
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
