/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.net.URL;

import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * plays a sound when exiting KeY
 * @author bubel
 */
public class ExitKeYSoundPlay extends PlaySound {

    /**
     * creates an action playing a sound when exiting KeY
     */
    public ExitKeYSoundPlay() {
        URL internalSoundFile = 
            KeYResourceManager.getManager().getResourceFile
            (NotificationTask.class, "sounds/exit.wav");
        if (internalSoundFile != null) {
            setSoundURL(internalSoundFile);
        }     
    }

}
