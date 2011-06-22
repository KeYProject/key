package de.uka.ilkd.key.gui.lemmatagenerator;

import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.SettingsListener;

public class LemmaGeneratorSettings implements de.uka.ilkd.key.gui.configuration.Settings{
        private LinkedList<SettingsListener> listeners = new LinkedList<SettingsListener>();
        private boolean showDialogAddingAxioms = true;
        private boolean showDialogUsingAxioms = true;
        private static final String SHOW_DIALOG_ADDING_AXIOMS = "[LemmaGenerator]showDialogWhenAddingAxioms";
        private static final String SHOW_DIALOG_USING_AXIOMS =  "[LemmaGenerator]showDialogWhenUsingTacletsAsAxioms";
        
        private boolean readBoolean(Properties properties, String key, boolean defaultValue){
                String value = properties.getProperty(key);
                if(value == null || !value.equals("true") || !value.equals("false")){
                        return defaultValue;
                }
                return value.equals("true");
        }
        
        private void writeBoolean(Properties properties, String key, boolean value){
                properties.setProperty(key,value ? "true" : "false");
        }
 
        private void fireSettingsChanged(){
                for(SettingsListener listener : listeners){
                        listener.settingsChanged(new GUIEvent(this));
                }
        }


        public boolean isShowingDialogAddingAxioms() {
                return showDialogAddingAxioms;
        }

        public void showDialogAddingAxioms(boolean value) {
                this.showDialogAddingAxioms = value;
                fireSettingsChanged();
        }

        public boolean isShowingDialogUsingAxioms() {
                return showDialogUsingAxioms;
        }

        public void showDialogUsingAxioms(boolean value) {
                this.showDialogUsingAxioms = value;
                fireSettingsChanged();
        }

        @Override
        public void addSettingsListener(SettingsListener l) {
               listeners.add(l);
        }

        @Override
        public void readSettings(Object sender, Properties props) {
               showDialogAddingAxioms = readBoolean(props,SHOW_DIALOG_ADDING_AXIOMS,true);
               showDialogUsingAxioms = readBoolean(props,SHOW_DIALOG_USING_AXIOMS,true);
        }

        @Override
        public void writeSettings(Object sender, Properties props) {
                writeBoolean(props,SHOW_DIALOG_ADDING_AXIOMS ,showDialogAddingAxioms);
                writeBoolean(props, SHOW_DIALOG_USING_AXIOMS, showDialogUsingAxioms);
                
        }

}
