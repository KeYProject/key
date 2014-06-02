// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Properties;
import java.util.Map.Entry;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.SettingsConverter;
import de.uka.ilkd.key.gui.configuration.SettingsListener;

import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverTypeCollection;

public class ProofIndependentSMTSettings implements de.uka.ilkd.key.gui.configuration.Settings, Cloneable {
	
        private static final String ACTIVE_SOLVER  = "[SMTSettings]ActiveSolver";

        private static final String TIMEOUT="[SMTSettings]SolverTimeout";


        private static final String PATH_FOR_SMT_TRANSLATION = "[SMTSettings]pathForSMTTranslation";

        private static final String PATH_FOR_TACLET_TRANSLATION = "[SMTSettings]pathForTacletTranslation";

        private static final String SHOW_SMT_RES_DIA="[SMTSettings]showSMTResDialog";



        private static final String PROGRESS_DIALOG_MODE = "[SMTSettings]modeOfProgressDialog";


        private static final String MAX_CONCURRENT_PROCESSES = "[SMTSettings]maxConcurrentProcesses";
        
        /* The following properties are used to set the bit sizes for bounded 
         * counter example generation.
         */
        private static final String INT_BOUND = "[SMTSettings]intBound";
        private static final String HEAP_BOUND = "[SMTSettings]heapBound";
        private static final String FIELD_BOUND = "[SMTSettings]fieldBound";
        private static final String OBJECT_BOUND = "[SMTSettings]objectBound";
        private static final String LOCSET_BOUND = "[SMTSettings]locsetBound";
        private static final int DEFAULT_BIT_LENGTH_FOR_CE_GENERATION = 3;        

   
        private static final String SOLVER_PARAMETERS  = "[SMTSettings]solverParametersV1";
        private static final String SOLVER_COMMAND       = "[SMTSettings]solverCommand";
        private static final String SOLVER_CHECK_FOR_SUPPORT  = "[SMTSettings]checkForSupport";
  
        public final static int    PROGRESS_MODE_USER = 0;
        public final static int    PROGRESS_MODE_CLOSE = 1;
        public final static int    PROGRESS_MODE_CLOSE_FIRST = 2;



        private final HashMap<SolverType,SolverData> dataOfSolvers =
                new LinkedHashMap<SolverType,SolverData>();
        public boolean showResultsAfterExecution    = false;
        public boolean storeSMTTranslationToFile    = false;
        public boolean storeTacletTranslationToFile = false;
        
        public long    timeout                      = 5000;
        public int     maxConcurrentProcesses       = 5;
    
        public int     modeOfProgressDialog         = PROGRESS_MODE_USER;

        public String   pathForSMTTranslation      = "";
        public String   pathForTacletTranslation   = "";
        public String   activeSolver               = "";
        


        public long intBound    = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
        public long heapBound   = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
        public long seqBound    = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
        public long objectBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
        public long locsetBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;

        private Collection<SettingsListener> listeners = new LinkedHashSet<SettingsListener>();
    
        private SolverTypeCollection activeSolverUnion = SolverTypeCollection.EMPTY_COLLECTION;
        private LinkedList<SolverTypeCollection> solverUnions = new LinkedList<SolverTypeCollection>();

		public boolean checkForSupport = true; 


        private ProofIndependentSMTSettings(ProofIndependentSMTSettings data) {
                copy(data);
        }
        
        
        
        public int getMaxConcurrentProcesses() {
			return maxConcurrentProcesses;
		}



		public void setMaxConcurrentProcesses(int maxConcurrentProcesses) {
			this.maxConcurrentProcesses = maxConcurrentProcesses;
		}



		public void copy(ProofIndependentSMTSettings data){
                this.showResultsAfterExecution     = data.showResultsAfterExecution;
                this.storeSMTTranslationToFile     = data.storeSMTTranslationToFile;
                this.storeTacletTranslationToFile  = data.storeTacletTranslationToFile;
                this.timeout                       = data.timeout;
                this.maxConcurrentProcesses        = data.maxConcurrentProcesses;
                this.pathForSMTTranslation         = data.pathForSMTTranslation;
                this.pathForTacletTranslation      = data.pathForTacletTranslation;
                this.modeOfProgressDialog          = data.modeOfProgressDialog;
                this.checkForSupport			   = data.checkForSupport;
                this.intBound                      = data.intBound;
                this.heapBound                     = data.heapBound;
                this.seqBound                      = data.seqBound;
                this.locsetBound                   = data.locsetBound;
                this.objectBound                   = data.objectBound;


                for(Entry<SolverType, SolverData> entry : data.dataOfSolvers.entrySet()){
                        dataOfSolvers.put(entry.getKey(), entry.getValue().clone());
                }
                solverUnions =  new LinkedList<SolverTypeCollection>(); 
                for(SolverTypeCollection solverUnion : data.solverUnions){
                        solverUnions.add(solverUnion);
                }   
        }


        private static final ProofIndependentSMTSettings DEFAULT_DATA = 
                new ProofIndependentSMTSettings();

        public static ProofIndependentSMTSettings getDefaultSettingsData(){
                return DEFAULT_DATA.clone();
        }

        public Collection<SolverType> getSupportedSolvers(){
                return dataOfSolvers.keySet();
        }

        private ProofIndependentSMTSettings() {
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
                return dataOfSolvers.get(type).solverParameters;
        }

        public void setCommand(SolverType type, String command){
                dataOfSolvers.get(type).solverCommand = command;
        }
        
        public void setParameters(SolverType type, String parameters){
            dataOfSolvers.get(type).solverParameters = parameters;
        }
        

        public Collection<SolverData> getDataOfSolvers(){
                return dataOfSolvers.values();
        }





        public ProofIndependentSMTSettings clone(){
                return new ProofIndependentSMTSettings(this);
        }



        public void readSettings(Object sender, Properties props){
                timeout = SettingsConverter.read(props, TIMEOUT, timeout);
                showResultsAfterExecution = SettingsConverter.read(props,SHOW_SMT_RES_DIA,showResultsAfterExecution);
                pathForSMTTranslation    = SettingsConverter.read(props, PATH_FOR_SMT_TRANSLATION, pathForSMTTranslation);
                pathForTacletTranslation = SettingsConverter.read(props, PATH_FOR_TACLET_TRANSLATION, pathForTacletTranslation);
                modeOfProgressDialog     = SettingsConverter.read(props,PROGRESS_DIALOG_MODE,modeOfProgressDialog);
                maxConcurrentProcesses   = SettingsConverter.read(props,MAX_CONCURRENT_PROCESSES,maxConcurrentProcesses);
                checkForSupport	         = SettingsConverter.read(props, SOLVER_CHECK_FOR_SUPPORT, checkForSupport);                
                intBound                 = SettingsConverter.read(props, INT_BOUND, intBound);
                heapBound                = SettingsConverter.read(props, HEAP_BOUND, heapBound);
                seqBound                 = SettingsConverter.read(props, FIELD_BOUND, seqBound);
                locsetBound              = SettingsConverter.read(props, LOCSET_BOUND, locsetBound);
                objectBound              = SettingsConverter.read(props, OBJECT_BOUND, objectBound);

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
                SettingsConverter.store(props,SOLVER_CHECK_FOR_SUPPORT,checkForSupport);
                SettingsConverter.store(props, INT_BOUND, intBound);
                SettingsConverter.store(props, HEAP_BOUND, heapBound);
                SettingsConverter.store(props, OBJECT_BOUND, objectBound);
                SettingsConverter.store(props, FIELD_BOUND, seqBound);
                SettingsConverter.store(props, LOCSET_BOUND, locsetBound);

                for(SolverData solverData : dataOfSolvers.values()){
                        solverData.writeSettings(props);
                }
        }
        



        public static class SolverData{
                public String solverParameters = "";
                public String solverCommand = "";
                public final SolverType type;
                
                public SolverData(SolverType type){
                        this(type,type.getDefaultSolverCommand(),type.getDefaultSolverParameters());
                       }

                private SolverData(SolverType type,String command, String parameters){
                        this.type = type;
                        this.solverCommand = command;
                        this.solverParameters = parameters;
                }

                private void readSettings(Properties props){

                        solverParameters = SettingsConverter.read(props,SOLVER_PARAMETERS+type.getName(),solverParameters);
                        solverCommand = SettingsConverter.read(props,SOLVER_COMMAND+type.getName(),solverCommand);
                        type.setSolverParameters(solverParameters);
                        type.setSolverCommand(solverCommand);

                }

                private void writeSettings(Properties props){
                        SettingsConverter.store(props,SOLVER_PARAMETERS+type.getName(),solverParameters);
                        SettingsConverter.store(props,SOLVER_COMMAND+type.getName(),solverCommand);
                        type.setSolverParameters(solverParameters);
                        type.setSolverCommand(solverCommand);
                }


                public SolverData clone(){
                        return new SolverData(type,solverCommand,solverParameters);
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
 
      }

@Override
public void addSettingsListener(SettingsListener l) {
        listeners.add(l);
        
  
}
}