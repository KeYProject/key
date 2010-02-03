// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/*
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.net.URL;

import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Plays a sound when the currently selected proof has been
 * closed
 * @author bubel
 */
public class ProofClosedSoundPlay extends PlaySound {

    /**
     * creates an instance of this notification action
     * 
     */
    public ProofClosedSoundPlay() {
        URL internalSoundFile = 
            KeYResourceManager.getManager().getResourceFile
        (NotificationTask.class, "sounds/trumpet.wav");
        if (internalSoundFile != null) {
            setSoundURL(internalSoundFile);
        }        
    }       
}
