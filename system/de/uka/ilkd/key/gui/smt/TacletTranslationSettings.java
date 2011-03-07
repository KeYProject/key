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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Properties;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;

/*
public class TacletTranslationSettings {
    private HashMap<String, Taclet> taclets =null;
    static private TacletTranslationSettings instance = new TacletTranslationSettings();
    public static TacletTranslationSettings getInstance(){
	return instance;
    }
    private LinkedList<SettingsListener> listener = new LinkedList<SettingsListener>();
  


    
    private TacletTranslationSettings(){
	
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

}*/
