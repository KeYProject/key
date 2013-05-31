// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui.smt;




import java.io.File;
import java.util.*;





import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.SettingsListener;


import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;



import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;


public class SMTSettings implements de.uka.ilkd.key.smt.SMTSettings{
        private final ProofDependentSMTSettings pdSettings;
        private final ProofIndependentSMTSettings piSettings;
        private final Proof proof;
        private LinkedList<Taclet> taclets = null;
        

        public SMTSettings(ProofDependentSMTSettings pdSettings,
                        ProofIndependentSMTSettings piSettings, Proof proof) {
                super();
                this.pdSettings = pdSettings;
                this.piSettings = piSettings;
                this.proof   = proof;
                
        }
        
        public void copy(SMTSettings settings){
                pdSettings.copy(settings.pdSettings);
                piSettings.copy(settings.piSettings);
                taclets = settings.taclets;
        }
        
        public ProofDependentSMTSettings getPdSettings() {
                return pdSettings;
        }
        
        public ProofIndependentSMTSettings getPiSettings() {
                return piSettings;
        }

        public Proof getProof() {
                return proof;
        }



        @Override
        public int getMaxConcurrentProcesses() {
                
                return piSettings.maxConcurrentProcesses;
        }

        @Override
        public int getMaxNumberOfGenerics() {
               
                return pdSettings.maxGenericSorts;
        }

        @Override
        public String getSMTTemporaryFolder() {
              return   PathConfig.getKeyConfigDir()
              + File.separator + "smt_formula";
        }

        @Override
        public Collection<Taclet> getTaclets() {
             if(taclets == null){
                     taclets = new LinkedList<Taclet>();
                     if(proof == null){
                             return taclets;
                     }
                     
                     for(Taclet taclet : proof.env().getInitConfig().activatedTaclets()){
                             if(pdSettings.supportedTaclets.contains(taclet.name().toString(),true)){
                                     taclets.add(taclet);
                             }
                     }
             }
             return taclets;  
        }

        @Override
        public long getTimeout() {
                
                return piSettings.timeout;
        }
        
       

        @Override
        public boolean instantiateNullAssumption() {
                
                return pdSettings.useNullInstantiation;
        }

        @Override
        public boolean makesUseOfTaclets() {
              
              return !getTaclets().isEmpty();

        }
        
        

        @Override
        public boolean useAssumptionsForBigSmallIntegers() {
               
                return pdSettings.useConstantsForIntegers;
        }

        @Override
        public boolean useBuiltInUniqueness() {
               
                return pdSettings.useBuiltInUniqueness;
        }

        @Override
        public boolean useExplicitTypeHierarchy() {
           
                return pdSettings.useExplicitTypeHierarchy;
        }

        @Override
        public boolean useUninterpretedMultiplicationIfNecessary() {
                
                return pdSettings.useUIMultiplication;
        }
        
        public SupportedTaclets getSupportedTaclets(){
                return pdSettings.supportedTaclets;
        }
        
        public int getModeOfProgressDialog(){
                return piSettings.modeOfProgressDialog;
        }
        
        public boolean storeSMTTranslationToFile(){
                return piSettings.storeSMTTranslationToFile;
        }
        
        public boolean storeTacletTranslationToFile(){
                return piSettings.storeTacletTranslationToFile;
        }
        
        public String getPathForTacletTranslation(){
                return piSettings.pathForTacletTranslation;
        }
        
        public String getPathForSMTTranslation(){
                return piSettings.pathForSMTTranslation;
        }
        
        public void fireSettingsChanged(){
                piSettings.fireSettingsChanged();
                pdSettings.fireSettingsChanged();
        }
        
        public void addListener(SettingsListener listener){
                piSettings.addSettingsListener(listener);
                pdSettings.addSettingsListener(listener);
        }

        @Override
        public long getMaximumInteger() {
                 return pdSettings.maxInteger;
        }

        @Override
        public long getMinimumInteger() {
                return pdSettings.minInteger;
        }

		@Override
		public String getLogic() {
			return "AUFLIA";
		}

		@Override
		public boolean checkForSupport() {
			return piSettings.checkForSupport;
		}

        

        
       
        
}


