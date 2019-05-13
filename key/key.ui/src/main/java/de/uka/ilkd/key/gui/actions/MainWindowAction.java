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
package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;

public abstract class MainWindowAction extends KeyAction {
    /**
     *
     */
    private static final long serialVersionUID = -6611537258325987383L;

    protected final MainWindow mainWindow;

    protected MainWindowAction(MainWindow mainWindow) {
        assert mainWindow != null;
        this.mainWindow = mainWindow;
        putValue(ACCELERATOR_KEY, KeyStrokeManager.get(this));
    }

    protected KeYMediator getMediator() {
        return mainWindow.getMediator();
    }
}
