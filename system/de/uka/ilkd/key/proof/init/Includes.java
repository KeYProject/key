// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.RuleSource;


/**
 * Encapsulates 2 lists (one for LDT-include, one for "normal" includes) 
 * containing the filenames parsed in the include-section of a <code>KeYFile</code>.
 * <code>name2Source</code> maps the entries of both lists to the corresponding
 * RuleSources.
 */ 
public class Includes{
    
    /** a list containing the "normal" includes, represented as Strings */
    private final List includes;
    /** a list containing the LDT includes, represented as Strings */
    private final List ldtIncludes;
    /** contains mappings from filenames to RuleSources */
    private final HashMap name2Source;

    public Includes(){
	includes = new LinkedList();
	ldtIncludes = new LinkedList();
	name2Source = new LinkedHashMap();
    }
    
    private void put(String name, RuleSource source, List list){
	if(!list.contains(name)){
	    list.add(name);
	    name2Source.put(name, source);
	}
    }

    /** adds a "normal" include.*/
    public void put(String name, RuleSource source){
	put(name, source, includes);
    }

    /** adds a LDT include.*/    
    public void putLDT(String name, RuleSource source){
	put(name, source, ldtIncludes);
    } 

    /** returns the corresponding RuleSource to the filename 
     * <code>name</name>
     */
    public RuleSource get(String name){
	return (RuleSource) name2Source.get(name);
    }

    /** removes the filename <code>name</code> and its mapping. */
    public void remove(String name){
	includes.remove(name);
	ldtIncludes.remove(name);
	name2Source.remove(name);
    }

    /** return the list of non-LDT includes*/ 
    public List getIncludes(){
	return includes;
    }

    /** return the list of LDT includes*/ 
    public List getLDTIncludes(){
	return ldtIncludes;
    }

    public boolean isEmpty(){
	return name2Source.isEmpty();
    }
    
    
    public void putAll(Includes in) {
	includes.addAll(in.includes);
	ldtIncludes.addAll(in.ldtIncludes);
	name2Source.putAll(in.name2Source);
    }
}
