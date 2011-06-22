package de.uka.ilkd.key.gui.smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Properties;
import java.util.Map.Entry;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.SettingsConverter;
import de.uka.ilkd.key.gui.configuration.SettingsListener;

import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverTypeCollection;

public class ProofIndependentSettings implements de.uka.ilkd.key.gui.configuration.Settings{
        private static final String ACTIVE_SOLVER  = "[SMTSettings]ActiveSolver";

        private static final String TIMEOUT="[SMTSettings]SolverTimeout";


        private static final String PATH_FOR_SMT_TRANSLATION = "[SMTSettings]pathForSMTTranslation";

        private static final String PATH_FOR_TACLET_TRANSLATION = "[SMTSettings]pathForTacletTranslation";

        private static final String SHOW_SMT_RES_DIA="[SMTSettings]showSMTResDialog";



        private static final String PROGRESS_DIALOG_MODE = "[SMTSettings]modeOfProgressDialog";


        private static final String MAX_CONCURRENT_PROCESSES = "[SMTSettings]maxConcurrentProcesses";

   
        private static final String EXECUTION_STRING  = "[SMTSettings]executionString";

  
        public final static int    PROGRESS_MODE_USER = 0;
        public final static int    PROGRESS_MODE_CLOSE = 1;
        public final static int    PROGRESS_MODE_CLOSE_FIRST = 2;



        private final HashMap<SolverType,SolverData> dataOfSolvers =
                new HashMap<SolverType,SolverData>();
        public boolean showResultsAfterExecution    = false;
        public boolean storeSMTTranslationToFile    = false;
        public boolean storeTacletTranslationToFile = false;
        
        public long    timeout                      = 5000;
        public int     maxConcurrentProcesses        = 5;
    
        public int     modeOfProgressDialog          = PROGRESS_MODE_USER;

        public String   pathForSMTTranslation      = "";
        public String   pathForTacletTranslation   = "";
        public String   activeSolver               = "";
    
        private LinkedList<SettingsListener> listeners = new LinkedList<SettingsListener>();

        private SolverTypeCollection activeSolverUnion = SolverTypeCollection.EMPTY_COLLECTION;
        private LinkedList<SolverTypeCollection> solverUnions = new LinkedList<SolverTypeCollection>(); 


        private ProofIndependentSettings(ProofIndependentSettings data) {
                copy(data);
        }
        
        public void copy(ProofIndependentSettings data){
                this.showResultsAfterExecution     = data.showResultsAfterExecution;
                this.storeSMTTranslationToFile     = data.storeSMTTranslationToFile;
                this.storeTacletTranslationToFile  = data.storeTacletTranslationToFile;
                this.timeout                       = data.timeout;
                this.maxConcurrentProcesses        = data.maxConcurrentProcesses;
                this.pathForSMTTranslation         = data.pathForSMTTranslation;
                this.pathForTacletTranslation      = data.pathForTacletTranslation;
                this.modeOfProgressDialog          = data.modeOfProgressDialog;


                for(Entry<SolverType, SolverData> entry : data.dataOfSolvers.entrySet()){
                        dataOfSolvers.put(entry.getKey(), entry.getValue().clone());
                }
                
                for(SolverTypeCollection solverUnion : data.solverUnions){
                        solverUnions.add(solverUnion);
                }   
        }


        private static final ProofIndependentSettings DEFAULT_DATA = 
                new ProofIndependentSettings();

        public static ProofIndependentSettings getDefaultSettingsData(){
                return DEFAULT_DATA.clone();
        }

        public Collection<SolverType> getSupportedSolvers(){
                return dataOfSolvers.keySet();
        }

        private ProofIndependentSettings() {
                dataOfSolvers.put(SolverType.Z3_SOLVER, new SolverData(SolverType.Z3_SOLVER));
                dataOfSolvers.put(SolverType.YICES_SOLVER, new SolverData(SolverType.YICES_SOLVER));
                dataOfSolvers.put(SolverType.SIMPLIFY_SOLVER, new SolverData(SolverType.SIMPLIFY_SOLVER));
                dataOfSolvers.put(SolverType.CVC3_SOLVER, new SolverData(SolverType.CVC3_SOLVER));
                solverUnions.add(new SolverTypeCollection("Z3",1,SolverType.Z3_SOLVER));
                solverUnions.add(new SolverTypeCollection("Yices",1,SolverType.YICES_SOLVER));
                solverUnions.add(new SolverTypeCollection("CVC3",1,SolverType.CVC3_SOLVER));
                solverUnions.add(new SolverTypeCollection("Simplify",1,SolverType.SIMPLIFY_SOLVER));
                solverUnions.add(new SolverTypeCollection("Multiple Solvers",2,SolverType.Z3_SOLVER,
                                SolverType.YICES_SOLVER,
                                SolverType.CVC3_SOLVER,
                                SolverType.SIMPLIFY_SOLVER));
        }




        public String getCommand(SolverType type){
                return dataOfSolvers.get(type).command;
        }

        public void setCommand(SolverType type, String command){
                dataOfSolvers.get(type).command = command;
        }

        public Collection<SolverData> getDataOfSolvers(){
                return dataOfSolvers.values();
        }





        public ProofIndependentSettings clone(){
                return new ProofIndependentSettings(this);
        }



        public void readSettings(Object sender, Properties props){
                timeout = SettingsConverter.read(props, TIMEOUT, timeout);
                showResultsAfterExecution = SettingsConverter.read(props,SHOW_SMT_RES_DIA,showResultsAfterExecution);
                pathForSMTTranslation    = SettingsConverter.read(props, PATH_FOR_SMT_TRANSLATION, pathForSMTTranslation);
                pathForTacletTranslation = SettingsConverter.read(props, PATH_FOR_TACLET_TRANSLATION, pathForTacletTranslation);
                modeOfProgressDialog     = SettingsConverter.read(props,PROGRESS_DIALOG_MODE,modeOfProgressDialog);
                maxConcurrentProcesses   = SettingsConverter.read(props,MAX_CONCURRENT_PROCESSES,maxConcurrentProcesses);

          
                for(SolverData solverData : dataOfSolvers.values()){
                        solverData.readSettings(props);
                }     
        }



    


        public void writeSettings(Object sender, Properties props){
                SettingsConverter.store(props,TIMEOUT,timeout);
                SettingsConverter.store(props,SHOW_SMT_RES_DIA,showResultsAfterExecution);
                SettingsConverter.store(props,PROGRESS_DIALOG_MODE,modeOfProgressDialog);
                SettingsConverter.store(props,PATH_FOR_SMT_TRANSLATION,pathForSMTTranslation);
                SettingsConverter.store(props,PATH_FOR_TACLET_TRANSLATION,pathForTacletTranslation);
                SettingsConverter.store(props,ACTIVE_SOLVER,activeSolver);
                SettingsConverter.store(props,MAX_CONCURRENT_PROCESSES,maxConcurrentProcesses);

                for(SolverData solverData : dataOfSolvers.values()){
                        solverData.writeSettings(props);
                }
        }
        



        public static class SolverData{
                public String command = "";
                public final SolverType type;
                public SolverData(SolverType type){
                        this.type = type;
                        command = type.getDefaultExecutionCommand();
                }

                private SolverData(SolverType type,String command){
                        this.type = type;
                        this.command = command;
                }

                private void readSettings(Properties props){

                        command = SettingsConverter.read(props,EXECUTION_STRING+type.getName(),command);
                        type.setExecutionCommand(command);

                }

                private void writeSettings(Properties props){
                        SettingsConverter.store(props,EXECUTION_STRING+type.getName(),command);
                        type.setExecutionCommand(command);
                }


                public SolverData clone(){
                        return new SolverData(type,command);
                }

                public String toString(){
                        return type.getName();
                }
        }
        
      public void setActiveSolverUnion(SolverTypeCollection solverUnion){
              if(activeSolverUnion != solverUnion){
                      activeSolverUnion = solverUnion;
                      activeSolver = activeSolverUnion.name();
                      fireSettingsChanged();
              }
      }

        public SolverTypeCollection computeActiveSolverUnion() {
                if (activeSolverUnion.isUsable()) {
                        return activeSolverUnion;
                }
                for (SolverTypeCollection solverUnion : solverUnions) {
                        if (solverUnion.isUsable()) {
                                setActiveSolverUnion(solverUnion);
                                return solverUnion;
                        }
                }
                setActiveSolverUnion(SolverTypeCollection.EMPTY_COLLECTION);
                return SolverTypeCollection.EMPTY_COLLECTION;
        }

        private SolverTypeCollection getSolverUnion(String name) {
                for (SolverTypeCollection union : solverUnions) {
                        if (union.name().equals(name)) {
                                return union;
                        }
                }
                return SolverTypeCollection.EMPTY_COLLECTION;
        }

        public Collection<SolverTypeCollection> getUsableSolverUnions() {
                LinkedList<SolverTypeCollection> unions = new LinkedList<SolverTypeCollection>();
                for (SolverTypeCollection union : getSolverUnions()) {
                        if (union.isUsable()) {
                                unions.add(union);
                        }
                }
                return unions;
        }

        public Collection<SolverTypeCollection> getSolverUnions() {
                return solverUnions;
        }
      
      public void fireSettingsChanged() {
              for (SettingsListener aListenerList : listeners) {
                      aListenerList.settingsChanged(new GUIEvent(this));
              }
              if(Main.instance != null){
                      Main.instance.updateSMTSelectMenu();
              }         
      }

@Override
public void addSettingsListener(SettingsListener l) {
        listeners.add(l);
        
  
}
}
