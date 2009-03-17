// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.net.URL;

import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Plays a sound to notify the user about an occured information message event 
 * @author bubel
 */
public class GeneralInformationSoundPlay extends PlaySound {

    /**
     * creates an action playing a warning sound in case of an
     * unexpected error
     */
    public GeneralInformationSoundPlay() {       
        URL internalSoundFile = 
            KeYResourceManager.getManager().getResourceFile
        (NotificationTask.class, "sounds/information.wav");
        if (internalSoundFile != null) {
            setSoundURL(internalSoundFile);
        }        
    }

}
