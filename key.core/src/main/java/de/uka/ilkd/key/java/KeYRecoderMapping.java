/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;


import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.util.Debug;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class KeYRecoderMapping {
    public static final Logger LOGGER = LoggerFactory.getLogger(KeYRecoderMapping.class);


    /** have special classes been parsed in */
    private boolean parsedSpecial = false;

    /**
     * maps a recoder programelement (or something similar, e.g. Type) to the KeY-equivalent
     */
    private final HashMap<Object, Object> map;

    /** maps a KeY programelement to the Recoder-equivalent */
    private final HashMap<Object, Object> revMap;

    /** a pseudo super class for all arrays used to declare length */
    private KeYJavaType superArrayType = null;


    public KeYRecoderMapping() {
        this.map = new LinkedHashMap<>(4096);
        this.revMap = new LinkedHashMap<>(4096);
    }


    /**
     * creates a KeYRecoderMapping object. Used for cloning and testing.
     *
     * @param map a HashMap mapping ProgramElements in Recoder to ProgramElements in KeY
     * @param revMap the reverse map (KeY->Recoder)
     * @param parsedSpecial boolean indicating if the special classes have been parsed in
     */
    KeYRecoderMapping(HashMap<Object, Object> map, HashMap<Object, Object> revMap,
            KeYJavaType superArrayType, boolean parsedSpecial) {
        this.map = map;
        this.revMap = revMap;
        this.superArrayType = superArrayType;
        this.parsedSpecial = parsedSpecial;
    }

    /**
     * returns a matching ProgramElement (KeY) to a given ProgramElement (Recoder)
     *
     * @param pe a recoder.java.ProgramElement
     */
    public ProgramElement toKeY(recoder.java.ProgramElement pe) {
        return (ProgramElement) map.get(pe);
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    public ModelElement toKeY(recoder.ModelElement pe) {
        return (ModelElement) map.get(pe);
    }


    /**
     * returns the Recoder-equivalent to a given ProgramElement (KeY). If there's no RecodeR
     * equivalent to program element pe, an assertion failure "Program Element <pe> not known" is
     * emitted.
     *
     * @param pe a JavaProgramElement
     */
    public recoder.java.ProgramElement toRecoder(ProgramElement pe) {
        Object res = revMap.get(pe);
        Debug.assertTrue(res != null, "Program Element not known", pe);
        return (recoder.java.ProgramElement) res;
    }


    /**
     * returns the Recoder-equivalent to a given ModelElement (KeY). If there's no
     * Recoder-equivalent to the ModelElement <code>pe</code> null is returned.
     *
     * @param pe a ModelElement
     */
    public recoder.ModelElement toRecoder(ModelElement pe) {
        return (recoder.ModelElement) revMap.get(pe);
    }

    public void put(Object rec, Object key) {
        Object formerValue = map.put(rec, key);
        Debug.assertTrue(formerValue == null, "keyrecodermapping: duplicate registration of type:",
            key);
        revMap.put(key, rec);
    }

    public boolean mapped(Object rec) {
        return map.containsKey(rec);
    }


    public Set<Object> elemsKeY() {
        return revMap.keySet();
    }

    public Set<Object> elemsRec() {
        return map.keySet();
    }

    public void setSuperArrayType(KeYJavaType superArrayType) {
        this.superArrayType = superArrayType;
    }

    public KeYJavaType getSuperArrayType() {
        return this.superArrayType;
    }


    @SuppressWarnings("unchecked")
    public KeYRecoderMapping copy() {
        return new KeYRecoderMapping((HashMap<Object, Object>) map.clone(),
            (HashMap<Object, Object>) revMap.clone(), superArrayType, parsedSpecial);
    }

    /**
     * As long as we do not support lemmata we need the source code of some 'java.lang' classes.
     * These are parsed in using method parseSpecial of {@link Recoder2KeY}. To avoid multiple
     * readings this method indicates whether the special have been parsed in or not.
     *
     * @return true if special classes have been parsed in
     */
    public boolean parsedSpecial() {
        return parsedSpecial;
    }

    public int size() {
        return map.size();
    }


    /**
     * As long as we do not support lemmata we need the source code of some 'java.lang' classes.
     * These are parsed in using method parseSpecial of {@link Recoder2KeY}. To avoid multiple
     * readings this method sets a flag whether the special have been parsed in or not
     *
     * @param b boolean indicating if the special classes have been parsed in
     */
    public void parsedSpecial(boolean b) {
        parsedSpecial = b;
    }

}
