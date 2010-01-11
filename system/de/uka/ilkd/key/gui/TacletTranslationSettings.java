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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;


public class TacletTranslationSettings implements Settings {
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
	tacletAssignmentToString((TreeNode)UsedTaclets.getTreeModel().getRoot()
		  , s);
	return s.toString();
    }
    
    private void tacletAssignmentToString(TreeNode node, StringBuffer buf){
	if(((TreeItem)((DefaultMutableTreeNode)node).getUserObject()).isChecked()){
	    buf.append("1");
	}
	else{
	    buf.append("0");
	}
	for(int i=0; i < node.getChildCount(); i++){
	    tacletAssignmentToString(node.getChildAt(i), buf);
	}
    }
    
    private void tacletAssignmentFromString(String s){
	tacletAssignmentFromString((TreeNode)UsedTaclets.getTreeModel().getRoot(),
		s, 0);
    }
    private int tacletAssignmentFromString(TreeNode node,String s, int index){
	if(index >= s.length() || index < 0) return -1;
	((TreeItem)((DefaultMutableTreeNode)node).getUserObject())
		.setChecked(s.charAt(index)=='1'?true:false);
	index++;
	for(int i=0; i < node.getChildCount(); i++){
	    index = tacletAssignmentFromString(node.getChildAt(i), s, index);
	    if(index == -1){
		break;
	    }
	}
	return index;
    }
    
    
    
    private void convertTacletAssignment(String s){
	Collection<TreeItem> items = UsedTaclets.getTreeItems();
	int i=0; 
	if(items.size() != s.length()) return;
	for(TreeItem item : items){
	  if(s.charAt(i)=='1'){
	      item.setChecked(true);
	  }
	  else{
	      item.setChecked(false);
	  }
	  i++;
	}
	UsedTaclets.validateParentSelection();
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
