// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.smt;

import java.io.File;
import java.util.*;
import java.util.Map.Entry;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.Taclet;


import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;


class SettingsData{
    private static final String ACTIVE_SOLVER  = "[SMTSettings]ActiveSolver";
    
    private static final String TIMEOUT="[SMTSettings]SolverTimeout";

    
    private static final String PATH_FOR_SMT_TRANSLATION = "[SMTSettings]pathForSMTTranslation";
    
    private static final String PATH_FOR_TACLET_TRANSLATION = "[SMTSettings]pathForTacletTranslation";
    
    private static final String SHOW_SMT_RES_DIA="[SMTSettings]showSMTResDialog";
    

    
    private static final String PROGRESS_DIALOG_MODE = "[SMTSettings]pd_mode";
    
    private static final String EXPLICIT_TYPE_HIERARCHY = "[SMTSettings]explicitTypeHierarchy";
    
    private static final String INSTANTIATE_NULL_PREDICATES = "[SMTSettings]instantiateNullPredicates";

    private static final String MAX_CONCURRENT_PROCESSES = "[SMTSettings]maxConcurrentProcesses";

    private static final String MAX_GENERIC_SORTS = "[SMTSettings]maxGenericSorts";
    
    private static final String EXECUTION_STRING  = "[SMTSettings]executionString";
    
    private static final String TACLET_SELECTION = "[SMTSettings]TacletSelection";
    
    public final static int    PROGRESS_MODE_USER = 0;
    public final static int    PROGRESS_MODE_CLOSE = 1;
    public final static int    PROGRESS_MODE_CLOSE_FIRST = 2;
    

    
    private final HashMap<SolverType,SolverData> dataOfSolvers =
	                                           new HashMap<SolverType,SolverData>();
    public boolean showResultsAfterExecution    = false;
    public boolean storeSMTTranslationToFile    = false;
    public boolean storeTacletTranslationToFile = false;
    public boolean useExplicitTypeHierarchy     = false;
    public boolean useNullInstantiation         = false;
    public long    timeout                      = 5000;
    public int     maxConcurrentProcesses        = 5;
    public int     maxGenericSorts               = 2;
    public int     modeOfProgressDialog          = 0;
   
    public String   pathForSMTTranslation      = "";
    public String   pathForTacletTranslation   = "";
    public String   activeSolver               = "";
    public String   tacletSelection            = "";
    

    private SettingsData(SettingsData data) {
	this.showResultsAfterExecution     = data.showResultsAfterExecution;
	this.storeSMTTranslationToFile     = data.storeSMTTranslationToFile;
	this.storeTacletTranslationToFile  = data.storeTacletTranslationToFile;
	this.useExplicitTypeHierarchy      = data.useExplicitTypeHierarchy;
	this.useNullInstantiation          = data.useNullInstantiation;
	this.timeout                       = data.timeout;
	this.maxConcurrentProcesses        = data.maxConcurrentProcesses;
	this.maxGenericSorts               = data.maxGenericSorts;
	this.pathForSMTTranslation         = data.pathForSMTTranslation;
	this.pathForTacletTranslation	   = data.pathForTacletTranslation;
	this.modeOfProgressDialog          = data.modeOfProgressDialog;
	this.tacletSelection	           = data.tacletSelection;
	
	
	for(Entry<SolverType, SolverData> entry : data.dataOfSolvers.entrySet()){
	    dataOfSolvers.put(entry.getKey(), entry.getValue().clone());
	}
    }
    
    
    private static final SettingsData DEFAULT_DATA = 
        new SettingsData();
   
    public static SettingsData getDefaultSettingsData(){
	return DEFAULT_DATA.clone();
    }
    
    public Collection<SolverType> getSupportedSolvers(){
	return dataOfSolvers.keySet();
    }
    
    private SettingsData() {
	dataOfSolvers.put(SolverType.Z3_SOLVER, new SolverData(SolverType.Z3_SOLVER));
	dataOfSolvers.put(SolverType.YICES_SOLVER, new SolverData(SolverType.YICES_SOLVER));
	dataOfSolvers.put(SolverType.SIMPLIFY_SOLVER, new SolverData(SolverType.SIMPLIFY_SOLVER));
	dataOfSolvers.put(SolverType.CVC3_SOLVER, new SolverData(SolverType.CVC3_SOLVER));

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
    
    
    
    
    
    public SettingsData clone(){
	return new SettingsData(this);
    }
    
    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	timeout = read(props, TIMEOUT, timeout);
	showResultsAfterExecution = read(props,SHOW_SMT_RES_DIA,showResultsAfterExecution);
        useExplicitTypeHierarchy = read(props,EXPLICIT_TYPE_HIERARCHY,
        	                                           useExplicitTypeHierarchy);
        useNullInstantiation = read(props,INSTANTIATE_NULL_PREDICATES,
        	                                       useNullInstantiation);
       	
    	pathForSMTTranslation    = read(props, PATH_FOR_SMT_TRANSLATION, pathForSMTTranslation);
    	pathForTacletTranslation =  read(props, PATH_FOR_TACLET_TRANSLATION, pathForTacletTranslation);
    	modeOfProgressDialog     = read(props,PROGRESS_DIALOG_MODE,modeOfProgressDialog);
    	maxConcurrentProcesses   = read(props,MAX_CONCURRENT_PROCESSES,maxConcurrentProcesses);
    	maxGenericSorts          = read(props,MAX_GENERIC_SORTS,maxGenericSorts);

    	activeSolver             = read(props,ACTIVE_SOLVER,activeSolver);
    	tacletSelection          = read(props,TACLET_SELECTION,tacletSelection);
    	
    	for(SolverData solverData : dataOfSolvers.values()){
    	    solverData.readSettings(props);
    	}
    	
    }
    
    
    public void writeSettings(Properties props) {	
        store(props,TIMEOUT,timeout);
        store(props,SHOW_SMT_RES_DIA,showResultsAfterExecution);
        store(props,EXPLICIT_TYPE_HIERARCHY,useExplicitTypeHierarchy);
        store(props,INSTANTIATE_NULL_PREDICATES,useNullInstantiation);
        store(props,PROGRESS_DIALOG_MODE,modeOfProgressDialog);
        store(props,PATH_FOR_SMT_TRANSLATION,pathForSMTTranslation);
        store(props,PATH_FOR_TACLET_TRANSLATION,pathForTacletTranslation);
        store(props,ACTIVE_SOLVER,activeSolver);
        store(props,MAX_CONCURRENT_PROCESSES,maxConcurrentProcesses);
        store(props,MAX_GENERIC_SORTS,maxGenericSorts);
        store(props,TACLET_SELECTION,tacletSelection);
        
    	for(SolverData solverData : dataOfSolvers.values()){
    	    solverData.writeSettings(props);
    	}
    	
    }
    

    
    private static String   read(Properties props, String key, String defaultVal){
	String eth = props.getProperty(key);
	return eth == null ? defaultVal : eth;
    }
    
    private static int     read(Properties props, String key, int defaultVal){
	String eth = props.getProperty(key);
	if(eth == null){
	    return defaultVal;
	}
	try{
	 return Integer.parseInt(eth);
	}catch (NumberFormatException e){
	  return defaultVal;
	}
    	
    }
    
    private static long    read(Properties props, String key, long defaultVal){
	String eth = props.getProperty(key);
	if(eth == null){
	    return defaultVal;
	}
	try{
	 return Long.parseLong(eth);
	}catch (NumberFormatException e){
	  return defaultVal;
	}
    }
    
    private static boolean read(Properties props, String key,boolean defaultVal){
        String eth = props.getProperty(key);
        if(eth == null){return defaultVal;}
        if(eth.equals("true")){return true;}
        if(eth.equals("false")){return false;}
        return defaultVal;
    }
    

    
    private static void store(Properties props,String key, String value){
	props.setProperty(key, value);
    }
    
    private static void store(Properties props,String key, boolean value){
	 props.setProperty(key,value ? "true" : "false");
    }
    
    private static void store(Properties props,String key, long value){
	 props.setProperty(key,Long.toString(value));
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
		
		command = read(props,EXECUTION_STRING+type.getName(),command);
		System.out.println("READ: "+ EXECUTION_STRING+type.getName()+" "+command);
		type.setExecutionCommand(command);
		
	    }
	    
	    private void writeSettings(Properties props){
		store(props,EXECUTION_STRING+type.getName(),command);
		type.setExecutionCommand(command);
	    }
	    
	    
	    public SolverData clone(){
		return new SolverData(type,command);
	    }
	    
	    public String toString(){
		return type.getName();
	    }
	}
    
}



/** This class encapsulates the information which 
 *  decision procedure should be used.
 */
public class SMTSettings implements Settings, de.uka.ilkd.key.smt.SMTSettings{
    /** the list of registered SettingListener */
    private LinkedList<SettingsListener> listenerList = new LinkedList<SettingsListener>();
   
    
    private SettingsData settingsData = SettingsData.getDefaultSettingsData();
    
     
    
    private Collection<Taclet>   tacletsForTranslation = null;
    private SolverTypeCollection activeSolverUnion = SolverTypeCollection.EMPTY_COLLECTION;
    private LinkedList<SolverTypeCollection> solverUnions = new LinkedList<SolverTypeCollection>(); 
    
    
    private static SMTSettings instance;
    
    private SMTSettings(){
	solverUnions.add(new SolverTypeCollection("Z3",1,SolverType.Z3_SOLVER));
	solverUnions.add(new SolverTypeCollection("Yices",1,SolverType.YICES_SOLVER));
	solverUnions.add(new SolverTypeCollection("CVC3",1,SolverType.CVC3_SOLVER));
	solverUnions.add(new SolverTypeCollection("Simplify",1,SolverType.SIMPLIFY_SOLVER));
	solverUnions.add(new SolverTypeCollection("Multiple Solvers",2,SolverType.Z3_SOLVER,
					SolverType.YICES_SOLVER,
					SolverType.CVC3_SOLVER,
					SolverType.SIMPLIFY_SOLVER));
	
    }
 

    
    public Collection<SolverType> getSupportedSolvers(){
	return settingsData.getSupportedSolvers();
    }
    
    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }
    

 
    

    public Collection<SolverTypeCollection> getSolverUnions(){
	return solverUnions;
    }
    
    public SolverTypeCollection computeActiveSolverUnion(){
	if(activeSolverUnion.isUsable()){
	    return activeSolverUnion;
	}
	for(SolverTypeCollection solverUnion : solverUnions){
	    if(solverUnion.isUsable()){
		setActiveSolverUnion(solverUnion);		
		return solverUnion;
	    }
	}
	setActiveSolverUnion(SolverTypeCollection.EMPTY_COLLECTION);
        return SolverTypeCollection.EMPTY_COLLECTION;
    }
    
    public void setActiveSolverUnion(SolverTypeCollection solverUnion){
	
	if(activeSolverUnion != solverUnion){
	    activeSolverUnion = solverUnion;
	    settingsData.activeSolver = activeSolverUnion.name();
	    fireSettingsChanged();
	}
    }



    
    
    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
	for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new GUIEvent(this));
        }
        if(Main.instance != null){
            Main.instance.updateSMTSelectMenu();
        }      
    }
    

    

    private SolverTypeCollection getSolverUnion(String name){
	for(SolverTypeCollection union : solverUnions){
	    if(union.name().equals(name)){
		return union;
	    }
	}
	return SolverTypeCollection.EMPTY_COLLECTION;
    }
    
    
    public Collection<SolverTypeCollection> getUsableSolverUnions(){
	LinkedList<SolverTypeCollection> unions = new LinkedList<SolverTypeCollection>();
	for(SolverTypeCollection union : getSolverUnions()){
	    if(union.isUsable()){
		unions.add(union);
	    }
	}
	return unions;
    }
    

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	System.out.println("READ SETTINGS");
	settingsData.readSettings(props);
	tacletAssignmentFromString(settingsData.tacletSelection);
	activeSolverUnion = getSolverUnion(settingsData.activeSolver);
    }
    
    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
	System.out.println("WRITE SETTINGS");
	settingsData.tacletSelection = tacletAssignmentToString();
	settingsData.activeSolver = computeActiveSolverUnion().name();
	settingsData.writeSettings(props);
    }
    
   
    /**
     * removes the specified listener form the listener list
     * @param l the listener
     */
    public void removeSettingsListener(SettingsListener l) {
	listenerList.remove(l);
    }   


    public static SMTSettings getInstance() {
	if (instance == null) {
	    instance = new SMTSettings();
	}	
	return instance;
    }

    public void setTacletsForTranslation(Collection<Taclet> taclets){
	if(taclets != null){
	    tacletsForTranslation = taclets;
	}
    }
    
    @Override
    public String getCommand(SolverType type) {
	return settingsData.getCommand(type);
    }

    @Override
    public int getMaxConcurrentProcesses() {
	return settingsData.maxConcurrentProcesses;
    }

    @Override
    public int getMaxNumberOfGenerics() {
	return settingsData.maxGenericSorts;
    }

    @Override
    public String getSMTTemporaryFolder() {
	return   PathConfig.KEY_CONFIG_DIR
	    + File.separator + "smt_formula";
    }

    @Override
    public Collection<Taclet> getTaclets(Services services) {
	if(tacletsForTranslation == null){
	    tacletsForTranslation = new LinkedList<Taclet>();
	    for(Taclet taclet : services.getProof().env().
		          getInitConfig().getTaclets()){
		tacletsForTranslation.add(taclet);
	    }
	}
	
        return tacletsForTranslation;
    }

    @Override
    public boolean instantiateNullAssumption() {
	return settingsData.useNullInstantiation;
    }

    @Override
    public boolean makesUseOfTaclets() {
	 	TreeItem item = ((TreeItem)((DefaultMutableTreeNode)UsedTaclets.INSTANCE.getTreeModel()
		.getRoot()).getUserObject());
	return item.getMode() == SelectionMode.all || item.getMode() == SelectionMode.user;

    }

    @Override
    public boolean useExplicitTypeHierarchy() {
	return settingsData.useExplicitTypeHierarchy;
    }
    
    @Override
    public long getTimeout() {
        return settingsData.timeout;
    }
    
    public boolean storeSMTTranslationToFile(){
	return settingsData.storeSMTTranslationToFile;
    }
    
    public boolean storeTacletTranslationToFile(){
	return settingsData.storeTacletTranslationToFile;
    }
    
    public String getPathForSMTTranslation(){
	return settingsData.pathForSMTTranslation;
    }
    
    public String getPathForTacletTranslation(){
	return settingsData.pathForTacletTranslation;
    }


    public SettingsData cloneData(){
	return settingsData.clone();
    }
    
    public void setData(SettingsData data){
	settingsData = data;
    }
    
    
    private String tacletAssignmentToString(){
	StringBuffer s= new StringBuffer();
	tacletAssignmentToString((TreeNode)UsedTaclets.INSTANCE.getTreeModel().getRoot()
		  , s);
	return s.toString();
    }
    
    private void tacletAssignmentToString(TreeNode node, StringBuffer buf){
	TreeItem item = ((TreeItem)((DefaultMutableTreeNode)node).getUserObject());
	

	buf.append(item.getMode().ordinal());
	
	for(int i=0; i < node.getChildCount(); i++){
	    tacletAssignmentToString(node.getChildAt(i), buf);
	}
    }
    
    private void tacletAssignmentFromString(String s){
	tacletAssignmentFromString((TreeNode)UsedTaclets.INSTANCE.getTreeModel().getRoot(),
		s, 0);
	UsedTaclets.INSTANCE.validateSelectionModes();
    }
    
    
    private int tacletAssignmentFromString(TreeNode node,String s, int index){
	if(index >= s.length() || index < 0) return -1;
	TreeItem item = ((TreeItem)((DefaultMutableTreeNode)node).getUserObject());
	
	String c = String.valueOf(s.charAt(index));

	
	if(Integer.valueOf(c) == SelectionMode.all.ordinal()){
	    item.setMode(SelectionMode.all);
	}else if(Integer.valueOf(c) == SelectionMode.user.ordinal()){
	    item.setMode(SelectionMode.user);
	}else{
	    item.setMode(SelectionMode.nothing);
	}

	index++;
	for(int i=0; i < node.getChildCount(); i++){
	    index = tacletAssignmentFromString(node.getChildAt(i), s, index);
	    if(index == -1){
		break;
	    }
	}
	return index;
    }
    



 

}
