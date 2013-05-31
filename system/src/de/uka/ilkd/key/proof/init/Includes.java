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


package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.io.RuleSource;


/**
 * Encapsulates 2 lists (one for LDT-include, one for "normal" includes)
 * containing the filenames parsed in the include-section of a <code>KeYFile</code>.
 * <code>name2Source</code> maps the entries of both lists to the corresponding
 * RuleSources.
 */
public class Includes {

    /** a list containing the "normal" includes, represented as Strings */
    private final List<String> includes;
    /** a list containing the LDT includes, represented as Strings */
    private final List<String> ldtIncludes;
    /** contains mappings from filenames to RuleSources */
    private final HashMap<String, RuleSource> name2Source;

    public Includes(){
	includes = new LinkedList<String>();
	ldtIncludes = new LinkedList<String>();
	name2Source = new LinkedHashMap<String, RuleSource>();
    }

    private void put(String name, RuleSource source, List<String> list){
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
	return name2Source.get(name);
    }

    /** removes the filename <code>name</code> and its mapping. */
    public void remove(String name){
	includes.remove(name);
	ldtIncludes.remove(name);
	name2Source.remove(name);
    }

    /** return the list of non-LDT includes*/
    public List<String> getIncludes(){
	return includes;
    }

    /** return the list of LDT includes*/
    public List<String> getLDTIncludes(){
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
