package de.uka.ilkd.key.gui.smt;


import java.util.LinkedList;
import java.util.Properties;


import de.uka.ilkd.key.gui.configuration.SettingsConverter;
import de.uka.ilkd.key.gui.configuration.SettingsListener;


public class ProofDependentSettings implements de.uka.ilkd.key.gui.configuration.Settings {

        private static final String EXPLICIT_TYPE_HIERARCHY = "[SMTSettings]explicitTypeHierarchy";

        private static final String INSTANTIATE_NULL_PREDICATES = "[SMTSettings]instantiateHierarchyAssumptions";


        private static final String MAX_GENERIC_SORTS = "[SMTSettings]maxGenericSorts";


        private static final String TACLET_SELECTION = "[SMTSettings]TacletSelection";

        private static final String USE_BUILT_IN_UNIQUENESS = "[SMTSettings]UseBuiltUniqueness";

        private static final String USE_UNINTERPRETED_MULTIPLICATION = "[SMTSettings]useUninterpretedMultiplication";

        private static final String USE_CONSTANTS_FOR_BIGSMALL_INTEGERS = "[SMTSettings]useConstantsForBigOrSmallIntegers";

        private LinkedList<SettingsListener> listeners = new LinkedList<SettingsListener>();

        public boolean useExplicitTypeHierarchy     = false;
        public boolean useNullInstantiation         = true;
        public boolean useBuiltInUniqueness          = false;
        public boolean useUIMultiplication          = true;
        public boolean useConstantsForIntegers     = true;
        public int     maxGenericSorts               = 2;
        public String   tacletSelection            = "";

        private ProofDependentSettings(){};

        private ProofDependentSettings(ProofDependentSettings data) {
                copy(data);
        }
        
        public void copy(ProofDependentSettings data){
                this.useExplicitTypeHierarchy      = data.useExplicitTypeHierarchy;
                this.useNullInstantiation          = data.useNullInstantiation;
                this.maxGenericSorts               = data.maxGenericSorts;
                this.tacletSelection               = data.tacletSelection;
                this.useBuiltInUniqueness          = data.useBuiltInUniqueness;
                this.useUIMultiplication           = data.useUIMultiplication;
                this.useConstantsForIntegers       = data.useConstantsForIntegers; 
        }


        private static final ProofDependentSettings DEFAULT_DATA = 
                new ProofDependentSettings();

        public static ProofDependentSettings getDefaultSettingsData(){
                return DEFAULT_DATA.clone();
        }


        
        public ProofDependentSettings clone(){
                return new ProofDependentSettings(this);
        }


        public void readSettings(Object sender, Properties props){

                useExplicitTypeHierarchy = SettingsConverter.read(props,EXPLICIT_TYPE_HIERARCHY,
                                useExplicitTypeHierarchy);
                useNullInstantiation = SettingsConverter.read(props,INSTANTIATE_NULL_PREDICATES,
                                useNullInstantiation);
                useBuiltInUniqueness = SettingsConverter.read(props,USE_BUILT_IN_UNIQUENESS,useBuiltInUniqueness);

                maxGenericSorts          = SettingsConverter.read(props,MAX_GENERIC_SORTS,maxGenericSorts);
                tacletSelection          = SettingsConverter.read(props,TACLET_SELECTION,tacletSelection);
                useUIMultiplication      = SettingsConverter.read(props,USE_UNINTERPRETED_MULTIPLICATION,useUIMultiplication);
                useConstantsForIntegers  = SettingsConverter.read(props,USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,useConstantsForIntegers);

        }

        public void writeSettings(Object sender, Properties props){
                SettingsConverter.store(props,EXPLICIT_TYPE_HIERARCHY,useExplicitTypeHierarchy);
                SettingsConverter.store(props,INSTANTIATE_NULL_PREDICATES,useNullInstantiation);
                SettingsConverter.store(props,MAX_GENERIC_SORTS,maxGenericSorts);
                SettingsConverter.store(props,TACLET_SELECTION,tacletSelection);
                SettingsConverter.store(props,USE_BUILT_IN_UNIQUENESS,useBuiltInUniqueness);
                SettingsConverter.store(props,USE_UNINTERPRETED_MULTIPLICATION,useUIMultiplication);
                SettingsConverter.store(props,USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,useConstantsForIntegers);
        }

        @Override
        public void addSettingsListener(SettingsListener l) {
               listeners.add(l);
                
        }
}
