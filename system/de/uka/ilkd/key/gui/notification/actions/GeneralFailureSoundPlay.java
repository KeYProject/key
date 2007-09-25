/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.io.File;
import java.net.URL;

import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Displays a warning sound when an unexpected failure occured. 
 * @author bubel
 */
public class GeneralFailureSoundPlay extends PlaySound {

    /**
     * creates an action playing a warning sound in case of an
     * unexpected error
     */
    public GeneralFailureSoundPlay() {       
        URL internalSoundFile = 
            KeYResourceManager.getManager().getResourceFile
        (NotificationTask.class, "sounds/error.wav");
        if (internalSoundFile != null) {
            setSoundFile(new File(internalSoundFile.getFile()));
        }        
    }

}
