package de.uka.ilkd.key.gui.configuration;

import javax.swing.JComponent;


public class ConfigChangeAdapter implements ConfigChangeListener {
    
    private final JComponent compRef;
    
    public ConfigChangeAdapter(JComponent comp){
        assert comp != null;
        compRef = comp;
    }
    
    public void configChanged(ConfigChangeEvent e) {
        compRef.updateUI();
    }
}
