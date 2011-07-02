package de.uka.ilkd.key.gui.smt;


import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Properties;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeNode;


import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.SettingsConverter;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem.SelectionMode;


public class ProofDependentSettings implements de.uka.ilkd.key.gui.configuration.Settings {

        private static final String EXPLICIT_TYPE_HIERARCHY = "[SMTSettings]explicitTypeHierarchy";

        private static final String INSTANTIATE_NULL_PREDICATES = "[SMTSettings]instantiateHierarchyAssumptions";


        private static final String MAX_GENERIC_SORTS = "[SMTSettings]maxGenericSorts";


        private static final String TACLET_SELECTION = "[SMTSettings]SelectedTaclets";

        private static final String USE_BUILT_IN_UNIQUENESS = "[SMTSettings]UseBuiltUniqueness";

        private static final String USE_UNINTERPRETED_MULTIPLICATION = "[SMTSettings]useUninterpretedMultiplication";

        private static final String USE_CONSTANTS_FOR_BIGSMALL_INTEGERS = "[SMTSettings]useConstantsForBigOrSmallIntegers";

        private Collection<SettingsListener> listeners = new HashSet<SettingsListener>();

        public boolean useExplicitTypeHierarchy     = false;
        public boolean useNullInstantiation         = true;
        public boolean useBuiltInUniqueness          = false;
        public boolean useUIMultiplication          = true;
        public boolean useConstantsForIntegers     = true;
        public int     maxGenericSorts               = 2;

        
       // public String []  tacletSelection            = new String[0];
        public  SupportedTaclets supportedTaclets;

        private ProofDependentSettings(){
 
                supportedTaclets =  SupportedTaclets.REFERENCE;
        };

        private ProofDependentSettings(ProofDependentSettings data) {            
                copy(data);                
        }
        
        public void copy(ProofDependentSettings data){
                supportedTaclets = new SupportedTaclets(data.supportedTaclets.getNamesOfSelectedTaclets());
                this.useExplicitTypeHierarchy      = data.useExplicitTypeHierarchy;
                this.useNullInstantiation          = data.useNullInstantiation;
                this.maxGenericSorts               = data.maxGenericSorts;
                this.useBuiltInUniqueness          = data.useBuiltInUniqueness;
                this.useUIMultiplication           = data.useUIMultiplication;
                this.useConstantsForIntegers       = data.useConstantsForIntegers; 
                System.out.println(supportedTaclets.ID);
             
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
               // tacletSelection          = SettingsConverter.read(props,TACLET_SELECTION,tacletSelection);
                useUIMultiplication      = SettingsConverter.read(props,USE_UNINTERPRETED_MULTIPLICATION,useUIMultiplication);
                useConstantsForIntegers  = SettingsConverter.read(props,USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,useConstantsForIntegers);
             
                supportedTaclets.selectTaclets(SettingsConverter.read(props, TACLET_SELECTION,
                                supportedTaclets.getNamesOfSelectedTaclets()));
        }

        public void writeSettings(Object sender, Properties props){
                SettingsConverter.store(props,EXPLICIT_TYPE_HIERARCHY,useExplicitTypeHierarchy);
                SettingsConverter.store(props,INSTANTIATE_NULL_PREDICATES,useNullInstantiation);
                SettingsConverter.store(props,MAX_GENERIC_SORTS,maxGenericSorts);
                SettingsConverter.store(props,TACLET_SELECTION,supportedTaclets.getNamesOfSelectedTaclets());
                SettingsConverter.store(props,USE_BUILT_IN_UNIQUENESS,useBuiltInUniqueness);
                SettingsConverter.store(props,USE_UNINTERPRETED_MULTIPLICATION,useUIMultiplication);
                SettingsConverter.store(props,USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,useConstantsForIntegers);
        }
        
        
        public void fireSettingsChanged() {
                for (SettingsListener aListenerList : listeners) {
                        aListenerList.settingsChanged(new GUIEvent(this));
                }
           //     if(MainWindow.hasInstance()){
              //          MainWindow.instance.updateSMTSelectMenu();
             //   }         
        }

        @Override
        public void addSettingsListener(SettingsListener l) {
               listeners.add(l);
                
        }
        

        
       
       /*  private void tacletAssignmentFromString(String s) {
        
                tacletAssignmentFromString((TreeNode)supportedTaclets
                                .getTreeModel().getRoot(), s, 0);
                supportedTaclets.validateSelectionModes();
        }*/

        private int tacletAssignmentFromString(TreeNode node, String s,
                        int index) {
                if (index >= s.length() || index < 0)
                        return -1;
                TreeItem item = ((TreeItem) ((DefaultMutableTreeNode) node)
                                .getUserObject());

                String c = String.valueOf(s.charAt(index));

                if (Integer.valueOf(c) == SelectionMode.all.ordinal()) {
                        item.setMode(SelectionMode.all);
                } else if (Integer.valueOf(c) == SelectionMode.user.ordinal()) {
                        item.setMode(SelectionMode.user);
                } else {
                        item.setMode(SelectionMode.nothing);
                }

                index++;
                for (int i = 0; i < node.getChildCount(); i++) {
                        index = tacletAssignmentFromString(node.getChildAt(i),
                                        s, index);
                        if (index == -1) {
                                break;
                        }
                }
                return index;
        }
}
