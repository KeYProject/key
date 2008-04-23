/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.net.URL;

import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * @author bubel
 */
public class AbandonTaskSoundPlay extends PlaySound {

    /**
     * creates an instance of this notification action     
     */
    public AbandonTaskSoundPlay() {
        URL internalSoundFile = 
            KeYResourceManager.getManager().getResourceFile
            (NotificationTask.class, "sounds/abandon.wav");
        if (internalSoundFile != null) {
            setSoundURL(internalSoundFile);
        }        
    }       
    

}
