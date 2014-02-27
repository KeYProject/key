// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;

public class FontSizeAction extends MainWindowAction implements ConfigChangeListener {
    
    /**
     * 
     */
    private static final long serialVersionUID = -5429097174272693359L;

    public static enum Mode { LARGER, SMALLER }

    private Mode mode;

    public FontSizeAction(MainWindow mainWindow, Mode mode) {
	super(mainWindow);
	this.mode = mode;
	
	setName(mode == Mode.LARGER ? "Larger" : "Smaller");
        setIcon(mode == Mode.LARGER ? IconFactory.plus(16): IconFactory.minus(16));
	
	int downMask = getDownMask();
	int key = mode == Mode.LARGER ? KeyEvent.VK_PLUS : KeyEvent.VK_MINUS;
        setAcceleratorKey(KeyStroke.getKeyStroke(key, downMask));
	
        Config.DEFAULT.addConfigChangeListener(this);
    }
    
    @Override
    public void actionPerformed(ActionEvent e) {
	switch (mode) {
        case LARGER:
            Config.DEFAULT.larger();
	    break;
	    
        case SMALLER:
            Config.DEFAULT.smaller();
	    break;
        }
    }

    @Override
    public void configChanged(ConfigChangeEvent e) {
	switch (mode) {
        case LARGER:
            setEnabled(!Config.DEFAULT.isMaximumSize());
	    break;
	    
        case SMALLER:
            setEnabled(!Config.DEFAULT.isMinimumSize());
	    break;
        }
    }

    /**
     * determine the key mask to use. (Probably this was a bug at a time)
     */
    private static int getDownMask() {
	int downMask = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
        switch (downMask) {
        case InputEvent.META_MASK : 
            downMask = InputEvent.META_DOWN_MASK; 
            break;        	
        default:
            // we default to Linux/Win
            downMask = InputEvent.CTRL_DOWN_MASK;
            break;
        }
	return downMask;
    }

   

}
