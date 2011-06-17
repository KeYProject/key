package de.uka.ilkd.key.gui.configuration;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringBufferInputStream;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmaGeneratorSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;


public class ProofIndependetSettings implements SettingsListener {
        public ProofIndependetSettings INSTANCE = new ProofIndependetSettings();
        private final SMTSettings smtSettings = new SMTSettings();
        private final LemmaGeneratorSettings lemmaGeneratorSettings = new LemmaGeneratorSettings();

        private final Settings[] settingsSet = { smtSettings,
                        lemmaGeneratorSettings };
        private boolean initialized = false;
        

        private ProofIndependetSettings() {
                for (Settings settings : settingsSet) {
                        settings.addSettingsListener(this);
                }
                loadSettings();
        }

        @Override
        public void settingsChanged(GUIEvent e) {
               saveSettings();

        }
        
        public void ensureInitialized() {
                if (!initialized) {
                    loadSettings();
                    initialized=true;   
                }
        }
        
        public LemmaGeneratorSettings getLemmaGeneratorSettings() {
                ensureInitialized();
                return lemmaGeneratorSettings;
        }
        
        public void loadSettings(){
                try {
                    FileInputStream in = new FileInputStream(PathConfig.PROOF_INDEPENDT_SETTINGS);
                    Properties properties = new Properties();
                    properties.load(in);
                    for(Settings settings : settingsSet){
                            settings.readSettings(properties);
                    }
                } catch (IOException e){
                        new RuntimeException(e);
                }
                initialized = true;
        }
        
        public void saveSettings(){
                ensureInitialized();
                try {
                    File file = new File(PathConfig.PROOF_INDEPENDT_SETTINGS);
                    if (!file.exists()) {                        
                            new File(PathConfig.KEY_CONFIG_DIR+File.separator).mkdirs();
                            file.createNewFile();
                    }            
                    FileOutputStream out = new FileOutputStream(file);
                   
                    Properties result = new Properties();
                    for (Settings settings : settingsSet) {
                            settings.writeSettings(result);
                    }
                    result.store(out, "Proof-Independent-Settings-File");
                    
                } catch (IOException e){
                    throw new RuntimeException(e);
                }
            
        }
      

        
        public SMTSettings getSMTSettings() {
                ensureInitialized();
                return smtSettings;
        }

}
