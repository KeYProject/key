package de.uka.ilkd.key.gui.utilities;

import java.awt.event.KeyEvent;
import java.util.Map;
import java.util.LinkedHashMap;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.macros.ProofMacro;

/**
 * Manages keyboard shortcuts for proof macros and GUI actions.
 * @author bruns
 *
 */
public final class KeyStrokeManager {
    
    private static Map<Class<?>, KeyStroke> mapping = new LinkedHashMap<Class<?>, KeyStroke>(30);
    
    // TODO: make replaceable
    static {
        mapping.put(de.uka.ilkd.key.gui.macros.FullAutoPilotProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F1,0));
        mapping.put(de.uka.ilkd.key.gui.macros.AutoPilotPrepareProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F2,0));
        mapping.put(de.uka.ilkd.key.gui.macros.PropositionalExpansionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F3,0));
        mapping.put(de.uka.ilkd.key.gui.macros.FullPropositionalExpansionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F4,0));
        mapping.put(de.uka.ilkd.key.gui.macros.TryCloseMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F5,0));
        mapping.put(de.uka.ilkd.key.gui.macros.FinishSymbolicExecutionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F6,0));
        mapping.put(de.uka.ilkd.key.gui.macros.OneStepProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F7,0));
    }
    
    public static KeyStroke get (ProofMacro macro) {
        return mapping.get(macro.getClass());
    }
    
    public static KeyStroke get (MainWindowAction action) {
        return mapping.get(action.getClass());
    }

}
