// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 03.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.io.File;
import java.net.MalformedURLException;

import de.uka.ilkd.key.gui.notification.NotificationAction;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.util.Debug;

/**
 * This notification action plays a sound.
 * @author bubel
 */
public class PlaySound implements NotificationAction {

    /** the file where the sound to play is stored */
    private File soundFile;
           
    public PlaySound() {        
    }
    
    /**
     * sets the file to be played
     * @param file the File to be played
     */
    public void setSoundFile(File file) {
        this.soundFile = file;
    }
    
    /**
     * plays the sound 
     * @see de.uka.ilkd.key.gui.notification.NotificationAction#execute(NotificationEvent)
     */
    public boolean execute(NotificationEvent event) {       
        if (soundFile != null) {
            try {               
                java.applet.Applet.newAudioClip(soundFile.toURL()).play();                
            } catch (MalformedURLException mue) {
                Debug.out("Failure playing soundfile ", mue);
                return false;
            } 
            return true;
        }
        Debug.out("No sound file found.");
        return false;
    }
    
}
