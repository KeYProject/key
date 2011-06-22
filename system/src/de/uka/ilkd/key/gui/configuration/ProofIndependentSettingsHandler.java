package de.uka.ilkd.key.gui.configuration;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaGeneratorSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSettings;



public class ProofIndependentSettingsHandler implements SettingsListener {
        public static final ProofIndependentSettingsHandler DEFAULT_INSTANCE = new ProofIndependentSettingsHandler(PathConfig.PROOF_INDEPENDT_SETTINGS);
        private final ProofIndependentSettings smtSettings = ProofIndependentSettings.getDefaultSettingsData();
        private final LemmaGeneratorSettings lemmaGeneratorSettings = new LemmaGeneratorSettings();
        private final String filename;

        private final Settings[] settingsSet = { smtSettings,
                        lemmaGeneratorSettings };

        

        private ProofIndependentSettingsHandler(String filename) {
                this.filename = filename;
                for (Settings settings : settingsSet) {
                        settings.addSettingsListener(this);
                }
                loadSettings(filename);
        }

        @Override
        public void settingsChanged(GUIEvent e) {
               saveSettings();

        }
        
   
        
        public LemmaGeneratorSettings getLemmaGeneratorSettings() {
                return lemmaGeneratorSettings;
        }
        
        public void loadSettings(String file){
                try {
                    FileInputStream in = new FileInputStream(PathConfig.PROOF_INDEPENDT_SETTINGS);
                    Properties properties = new Properties();
                    properties.load(in);
                    for(Settings settings : settingsSet){
                            settings.readSettings(this,properties);
                    }
                } catch (IOException e){
                        new RuntimeException(e);
                }
      
        }
        
        public void saveSettings(){
              
                try {
                    File file = new File(filename);
                    if (!file.exists()) {                        
                            new File(PathConfig.KEY_CONFIG_DIR+File.separator).mkdirs();
                            file.createNewFile();
                    }            
                    FileOutputStream out = new FileOutputStream(file);
                   
                    Properties result = new Properties();
                    for (Settings settings : settingsSet) {
                            settings.writeSettings(this,result);
                    }
                    result.store(out, "Proof-Independent-Settings-File");
                    
                } catch (IOException e){
                    throw new RuntimeException(e);
                }
            
        }
      

        
        public ProofIndependentSettings getSMTSettings() {
               return smtSettings;
        }

}
