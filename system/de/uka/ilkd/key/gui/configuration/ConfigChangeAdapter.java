package de.uka.ilkd.key.gui.configuration;

import java.lang.ref.WeakReference;

import javax.swing.JComponent;


public class ConfigChangeAdapter implements ConfigChangeListener {
    WeakReference<JComponent> compRef;
    
    public ConfigChangeAdapter(JComponent comp){
        compRef = new WeakReference<JComponent>(comp);
    }
    
    public void clear(){
        compRef=null;
    }
    
    public void configChanged(ConfigChangeEvent e) {
         JComponent comp = compRef.get();
         if(comp!=null)
             comp.updateUI();
    }
}
