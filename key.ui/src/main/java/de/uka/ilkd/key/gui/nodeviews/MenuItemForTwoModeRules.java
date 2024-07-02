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

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;


public class MenuItemForTwoModeRules extends JMenu implements
        BuiltInRuleMenuItem {

    private static final int EXPAND_DELAY = 200;
    private static final long serialVersionUID = 2183229438545523499L;

    // without selecting one the options above take unforced mode as default
    private static final boolean DEFAULT_FORCE = true;
    
    private final BuiltInRule rule;
    private boolean forcedMode = DEFAULT_FORCE;
    // we support only one listener
    private ActionListener listener;
    
    public MenuItemForTwoModeRules(String mainName, 
            String actionTextForForcedMode, String tooltipForcedMode,
            String actionTextForInteractiveMode, String tooltipInteractiveMode,  
            BuiltInRule rule) {
        super(mainName);
        
        this.rule = rule;
                
        init(actionTextForForcedMode, tooltipForcedMode, 
                actionTextForInteractiveMode, tooltipInteractiveMode);    
    }
    
    private void init(String actionTextForForcedMode, String tooltipForcedMode,
            String actionTextForInteractiveMode, String tooltipInteractiveMode) {
        
        JMenuItem forcedModeItem = new JMenuItem(actionTextForForcedMode);
        forcedModeItem.setToolTipText(tooltipForcedMode);
        add(forcedModeItem);
        forcedModeItem.addActionListener(new ActionListener() {            
            @Override
            public void actionPerformed(ActionEvent e) {
                forcedMode = true;
                listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this, 
                        ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
            }
        });

        
        JMenuItem interactiveModeItem = new JMenuItem(actionTextForInteractiveMode);
        interactiveModeItem.setToolTipText(tooltipInteractiveMode);
        add(interactiveModeItem);
        interactiveModeItem.addActionListener(new ActionListener() {            
            @Override
            public void actionPerformed(ActionEvent e) {
                forcedMode = false;
                listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this, 
                        ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
            }
        });
        
        
        // without selecting one the options above take forced mode as default
        
        super.addActionListener(new ActionListener() {
            
            @Override
            public void actionPerformed(ActionEvent e) {
                forcedMode = DEFAULT_FORCE;
                listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this, 
                        ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
            }
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