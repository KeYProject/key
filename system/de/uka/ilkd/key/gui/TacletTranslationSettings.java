// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;


public class TacletTranslationSettings implements Settings {
    private HashMap<String, Taclet> taclets =null;
    static private TacletTranslationSettings instance = new TacletTranslationSettings();
    public static TacletTranslationSettings getInstance(){
	return instance;
    }
    private LinkedList<SettingsListener> listener = new LinkedList<SettingsListener>();
  
    private static final String KEY_FILENAME = "[TacletTranslation]filename";
    private static final String KEY_SAVE_TO_FILE = "[TacletTranslation]saveToFile";
    private static final String KEY_MAX_GENERIC = "[TacletTranslation]maxGeneric";
    private static final String KEY_ASSIGNMENT  = "[TacletTranslation]assignment";
    private int maxGeneric=2;
    private String filename;
    private boolean saveToFile= false;
    
    public int getMaxGeneric() {
        return maxGeneric;
    }


    public void setMaxGeneric(int maxGeneric) {
        this.maxGeneric = maxGeneric;
    }


    public String getFilename() {
        return filename;
    }


    public void setFilename(String filename) {
        this.filename = filename;
    }


    public boolean isSaveToFile() {
        return saveToFile;
    }


    public void setSaveToFile(boolean saveToFile) {
        this.saveToFile = saveToFile;
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
    
    

    
    public boolean isUsingTaclets(){
	TreeItem item = ((TreeItem)((DefaultMutableTreeNode)UsedTaclets.INSTANCE.getTreeModel()
		.getRoot()).getUserObject());
	return item.getMode() == SelectionMode.all || item.getMode() == SelectionMode.user;

    }
    
    public Collection<Taclet> initTaclets(TacletIndex tacletIndex){
	
	
	return initTacletMap(tacletIndex).values();
    }
    
    public HashMap<String,Taclet> initTacletMap(TacletIndex tacletIndex){
	if(taclets==null){
	    taclets = new HashMap<String,Taclet>();


	    final ImmutableSet<NoPosTacletApp> apps =  tacletIndex.allNoPosTacletApps();
	    for (final NoPosTacletApp app : apps){
		taclets.put(app.taclet().name().toString(),app.taclet());

	    }

	}
	return taclets;
    }
    
    public HashMap<String,Taclet> initTacletMap(ImmutableSet<Taclet> tac){
	if(taclets==null){
	    taclets = new HashMap<String,Taclet>();


	    
	    for (Taclet t : tac){
		taclets.put(t.name().toString(),t);

	    }

	}
	return taclets;
    }
    
    public HashMap<String, Taclet> getTacletMap(){
	return taclets;
    }
    
    

    
    
  
    public void addSettingsListener(SettingsListener l) {
	listener.add(l);
	
    }
    
    
    public void fireSettingsHaveChanged(){
	for(SettingsListener l : listener){
	    l.settingsChanged(new GUIEvent(this));
	}
    }


    public void readSettings(Properties props) {
	saveToFile = Boolean.valueOf(props.getProperty(KEY_SAVE_TO_FILE,"false"));
	maxGeneric = Integer.valueOf(props.getProperty(KEY_MAX_GENERIC,"2"));
	filename = props.getProperty(KEY_FILENAME,"");
	tacletAssignmentFromString(props.getProperty(KEY_ASSIGNMENT, ""));
	
	
	
    }
    


    public void writeSettings(Properties props) {
	props.setProperty(KEY_SAVE_TO_FILE,Boolean.toString(saveToFile));
	props.setProperty(KEY_MAX_GENERIC,Integer.toString(maxGeneric));
	props.setProperty(KEY_FILENAME, filename);
	props.setProperty(KEY_ASSIGNMENT,tacletAssignmentToString());
	
	
    }

}
