package de.uka.ilkd.key.gui.utilities;

import java.util.Map;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.macros.ProofMacro;

public final class KeyStrokeManager {
    
    private static Map<Class<?>, KeyStroke> mapping;
    
    public static KeyStroke get (ProofMacro macro) {
        return mapping.get(macro.getClass());
    }

}
