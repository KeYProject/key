/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import javax.swing.*;

import de.uka.ilkd.key.rule.BuiltInRule;


public class MenuItemForTwoModeRules extends JMenu implements BuiltInRuleMenuItem {

    private static final int EXPAND_DELAY = 200;
    private static final long serialVersionUID = 2183229438545523499L;

    // without selecting one the options above take unforced mode as default
    private static final boolean DEFAULT_FORCE = true;

    private final BuiltInRule rule;
    private boolean forcedMode = DEFAULT_FORCE;
    // we support only one listener
    private ActionListener listener;

    public MenuItemForTwoModeRules(String mainName, String actionTextForForcedMode,
            String tooltipForcedMode, String actionTextForInteractiveMode,
            String tooltipInteractiveMode, BuiltInRule rule) {
        super(mainName);

        this.rule = rule;

        init(actionTextForForcedMode, tooltipForcedMode, actionTextForInteractiveMode,
            tooltipInteractiveMode);
    }

    private void init(String actionTextForForcedMode, String tooltipForcedMode,
            String actionTextForInteractiveMode, String tooltipInteractiveMode) {

        JMenuItem forcedModeItem = new JMenuItem(actionTextForForcedMode);
        forcedModeItem.setToolTipText(tooltipForcedMode);
        add(forcedModeItem);
        forcedModeItem.addActionListener(e -> {
            forcedMode = true;
            listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this,
                ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
        });


        JMenuItem interactiveModeItem = new JMenuItem(actionTextForInteractiveMode);
        interactiveModeItem.setToolTipText(tooltipInteractiveMode);
        add(interactiveModeItem);
        interactiveModeItem.addActionListener(e -> {
            forcedMode = false;
            listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this,
                ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
        });


        // without selecting one the options above take forced mode as default

        super.addActionListener(e -> {
            forcedMode = DEFAULT_FORCE;
            listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this,
                ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
        });

        // wait a bit longer before expanding submenus
        setDelay(getDelay() + EXPAND_DELAY);

        super.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                forcedMode = DEFAULT_FORCE;

                listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this,
                    ActionEvent.ACTION_PERFORMED, getText()));
                MenuItemForTwoModeRules.this.getParent().setVisible(false);
            }
        });


    }


    @Override
    public void addActionListener(ActionListener al) {
        this.listener = al;
    }


    @Override
    public void removeActionListener(ActionListener al) {
        if (this.listener == al) {
            this.listener = null;
        }
    }

    @Override
    public BuiltInRule connectedTo() {
        return rule;
    }

    @Override
    public boolean forcedApplication() {
        return forcedMode;
    }

}
