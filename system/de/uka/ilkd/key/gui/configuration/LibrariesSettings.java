// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.configuration;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.gui.GUIEvent;

/** This class encapsulates the information about the active
 * libraries settings
 */
public class LibrariesSettings implements Settings {

   private static final String LIBRARIES_KEY = "[Libraries]Default";
   private static final String LIBRARIES_PATH = "libraries"+File.separator;
   private LinkedList listenerList = new LinkedList();

   /** keys:   the file names of the libraries,
    *          standard libraries are given by the library name
    *          and user libraries are given by the absolute path
    *  values: Booleans that indicate if a library is selected
    */
   private HashMap libToSel = new HashMap();
   
   /** this boolean indicates that there was no "Libraries" properties section,
    *  we need this because the there at least the standard libraries in
    *  in the libaries settings*/
   private boolean emptyProperties=true;
   
   private static String[] standardLibs= {"stringRules.key", "deprecatedRules.key", "acc.key"};
   
   public LibrariesSettings(){
       /*adds the standard libraries to libToSel, maybe they will be
         replaced by readSettings  */ 
       for(int i=0;i<standardLibs.length;i++){
               libToSel.put(standardLibs[i],new Boolean(false));
           }     
   }
   
   
   
   /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings.
     */
    public void readSettings(Properties props) {
        String librariesSequence = props.getProperty(LIBRARIES_KEY);
        emptyProperties=false;
        if (librariesSequence != null){
            StringTokenizer st = new StringTokenizer(librariesSequence, ",");
            while (st.hasMoreTokens()) {
                String token = st.nextToken().trim();
                int sepIndex = token.lastIndexOf("-"); 
                if ((sepIndex > 0) && (sepIndex < token.length()-1))
                    libToSel.put(token.substring(0,sepIndex).trim(),
                            new Boolean(token.substring(sepIndex+1).trim()));
            }
        } else emptyProperties=true;
    }


    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
	String s="";
	Iterator keyIt = libToSel.keySet().iterator();
	while (keyIt.hasNext()){
           String fileName = (String) keyIt.next();
           String sel =  libToSel.get(fileName).toString();           
           s+=fileName+"-"+sel;
           if (keyIt.hasNext())
               s+=", ";
       }
      props.setProperty(LIBRARIES_KEY,s);		       
   }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        Iterator it = listenerList.iterator();
	while (it.hasNext()) {
	    ((SettingsListener)it.next()).settingsChanged(new GUIEvent(this));
	}
    }

    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }
    
    public HashMap getLibraries(){
        return (HashMap)libToSel.clone();
    }
    
    public void setLibraries(HashMap libraries){
        HashMap oldLibToSel = this.libToSel;
        this.libToSel = libraries;
        if(oldLibToSel!=null && 
           !oldLibToSel.equals(libToSel)){
            fireSettingsChanged();
        }        
        
    }
    
    public boolean emptyProperties(){
        return emptyProperties;
    }
    
    /** @return the path of the libraries */
    public static String getLibrariesPath(){
        return LIBRARIES_PATH;
    }

}
