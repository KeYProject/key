/*
 * Created on 03.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.net.URL;

import de.uka.ilkd.key.gui.notification.NotificationAction;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.util.Debug;

/**
 * This notification action plays a sound.
 * @author bubel
 */
public class PlaySound implements NotificationAction {

    /** the URL where to find the sound file to play */
    private URL soundURL;
           
    public PlaySound() {        
    }
    
    /**
     * sets the URL pointing to the location of the sound to be played
     * @param url the URL refering to the sound to be played
     */
    public void setSoundURL(URL url) {
        this.soundURL = url;
    }
    
    /**
     * plays the sound 
     * @see de.uka.ilkd.key.gui.notification.NotificationAction#execute(NotificationEvent)
     */
    public boolean execute(NotificationEvent event) {       
        if (soundURL != null) {       
            java.applet.Applet.newAudioClip(soundURL).play();            
            return true;
        }
        Debug.out("No sound file found.");
        return false;
    }
    
}
