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

    private static final long serialVersionUID = 2183229438545523499L;
    
    private final BuiltInRule rule;
    private boolean forcedMode = true;
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
                forcedMode = true;
                listener.actionPerformed(new ActionEvent(MenuItemForTwoModeRules.this, 
                        ActionEvent.ACTION_PERFORMED, e.getActionCommand()));
            }
        });

        // wait a bit longer before expanding submenus
        setDelay(getDelay() + 500);
        
        super.addMouseListener(new MouseAdapter() {            
            @Override
            public void mouseClicked(MouseEvent e) {
                forcedMode = true;
                
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
