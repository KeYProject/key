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

package de.uka.ilkd.key.java;


import java.util.HashMap;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.util.Debug;



public class KeYRecoderMapping{


    /** have special classes been parsed in */
    private boolean parsedSpecial = false;

    /** maps a recoder programelement (or something similar, e.g. Type)
    * to the KeY-equivalent
    */
    private HashMap map;

    /** maps a KeY programelement to the Recoder-equivalent */
    private HashMap revMap;

    /** a pseudo super class for all arrays used to declare length */
    private KeYJavaType superArrayType=null;

    
    public KeYRecoderMapping() {
	this.map = new HashMap();
	this.revMap = new HashMap();
    }


    /**
    * creates a KeYRecoderMapping object.
    * Used for cloning and testing.
    * @param map a HashMap mapping ProgramElements in Recoder to
    * ProgramElements in KeY
    * @param revMap the reverse map (KeY->Recoder)
    * @param parsedSpecial boolean indicating if the special classes have been parsed in
    */
    KeYRecoderMapping(HashMap map, HashMap revMap,
                             KeYJavaType superArrayType,
			     boolean parsedSpecial){
        this.map      = map;
        this.revMap   = revMap;
        this.superArrayType = superArrayType;
	this.parsedSpecial = parsedSpecial;
    }

    /**
    * returns a matching ProgramElement (KeY) to a given
    * ProgramElement (Recoder)
    * @param pe a recoder.java.ProgramElement
    */
    public ProgramElement toKeY(recoder.java.ProgramElement pe) {
        return (ProgramElement)map.get(pe);
    }

    /**
    * returns a matching ModelElement (KeY) to a given recoder.ModelElement
    * @param pe a recoder.ModelElement
    */
    public ModelElement toKeY(recoder.ModelElement pe) {
        return (ModelElement)map.get(pe);
    }


    /**
    * returns the Recoder-equivalent to a given ProgramElement (KeY).
    * If there's no RecodeR equivalent to program element pe, an
    * assertion failure "Program Element <pe> not known" is emitted.
    * @param pe a JavaProgramElement
    */
    public recoder.java.ProgramElement toRecoder(ProgramElement pe) {
        Object res=revMap.get(pe);
        Debug.assertTrue(res!=null, "Program Element not known", pe);
        return (recoder.java.ProgramElement)res;
    }


    /**
    * returns the Recoder-equivalent to a given ModelElement (KeY).
    * If there's no Recoder-equivalent to the ModelElement pe a
    * debug message "Model Element <pe> not known" is printed.
    * @param pe a ModelElement
    */
    public recoder.ModelElement toRecoder(ModelElement pe) {
        Object res=revMap.get(pe);
	if (res==null) {
	    //System.out.println(revMap);
	}
        Debug.assertTrue(res!=null, "Model Element not known", pe);	

        return (recoder.ModelElement)res;
    }

    public void put(Object rec, Object key) {
	Object formerValue = map.put(rec, key);
	Debug.assertTrue(formerValue == null, 
			 "keyrecodermapping: duplicate registration of type:", key);
	revMap.put(key, rec);
    }

    public boolean mapped(Object rec) {
	return map.containsKey(rec);
    }
    

    public Set elemsKeY() {
	return revMap.keySet();
    }

    public Set elemsRec() {
	return map.keySet();
    }

    public void setSuperArrayType(KeYJavaType superArrayType) {
        this.superArrayType = superArrayType;
    }

    public KeYJavaType getSuperArrayType() {
        return this.superArrayType;
    }

    
    public KeYRecoderMapping copy() {
	return new KeYRecoderMapping((HashMap)map.clone(), 
				     (HashMap)revMap.clone(),
                                     superArrayType,
				     parsedSpecial);
    }

    /**
     * As long as we do not support lemmata we need the source code of
     * some 'java.lang' classes. These are parsed in using method
     * parseSpecial of {@link Recoder2KeY}. To avoid multiple readings
     * this method indicates whether the special have been parsed in or
     * not. 
     * @return true if special classes have been parsed in
     */
    public boolean parsedSpecial() {
	return parsedSpecial;
    }

    public int size(){
	return map.size();
    }
    

    /**
     * As long as we do not support lemmata we need the source code of
     * some 'java.lang' classes. These are parsed in using method
     * parseSpecial of {@link Recoder2KeY}. To avoid multiple readings
     * this method sets a flag whether the special have been parsed in or
     * not
     * @param b boolean indicating if the special classes have been
     * parsed in
     */
    public void parsedSpecial(boolean b) {
	parsedSpecial = b;
    }

}
