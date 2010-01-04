// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;


public class TreeItem {
    private String text;
    private boolean checked = true;
    private boolean parentSelected = true;
    
    TreeItem(String text){
	this.text = text;
    }
    
    TreeItem(String text, boolean checked){
	this.text = text;
	this.checked = checked;
    
    }
    
    public boolean isChecked(){
	return checked;
    }
    
    public void setChecked(boolean b){
	checked = b;
    }

    public String toString(){
	return text;
    }
    
    public int hashCode(){
	return text.hashCode();
    }
    
    public boolean isParentSelected(){
	return parentSelected;
    }
    
    public void setParentSelected(boolean b){
	parentSelected = b;
    }
    
    
    
    
}