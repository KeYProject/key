package de.uka.ilkd.key.java;

import com.github.javaparser.ast.Node;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.util.Debug;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class KeyJPMapping {
    public static final Logger LOGGER = LoggerFactory.getLogger(KeyJPMapping.class);

    /**
     * have special classes been parsed in
     */
    private boolean parsedSpecial = false;

    /**
     * maps a recoder programelement (or something similar, e.g. Type)
     * to the KeY-equivalent
     */
    private final HashMap<Node, ModelElement> map;

    /**
     * maps a KeY programelement to the Recoder-equivalent
     */
    private final Map<ModelElement, Node> revMap;

    /**
     * a pseudo super class for all arrays used to declare length
     */
    private KeYJavaType superArrayType = null;


    public KeyJPMapping() {
        this.map = new LinkedHashMap<>(4096);
        this.revMap = new LinkedHashMap<>(4096);
    }


    /**
     * creates a KeYRecoderMapping object.
     * Used for cloning and testing.
     *
     * @param map           a HashMap mapping ProgramElements in Recoder to
     *                      ProgramElements in KeY
     * @param revMap        the reverse map (KeY->Recoder)
     * @param parsedSpecial boolean indicating if the special classes have been parsed in
     */
    KeyJPMapping(HashMap<Node, ModelElement> map, Map<ModelElement, Node> revMap,
                 KeYJavaType superArrayType,
                 boolean parsedSpecial) {
        this.map = map;
        this.revMap = revMap;
        this.superArrayType = superArrayType;
        this.parsedSpecial = parsedSpecial;
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    public ModelElement toKeY(Node pe) {
        return map.get(pe);
    }


    /**
     * returns the Recoder-equivalent to a given ProgramElement (KeY).
     * If there's no RecodeR equivalent to program element pe, an
     * assertion failure "Program Element <pe> not known" is emitted.
     *
     * @param pe a JavaProgramElement
     */
    public Node toRecoder(ProgramElement pe) {
        Node res = revMap.get(pe);
        Debug.assertTrue(res != null, "Program Element not known", pe);
        return res;
    }


    /**
     * returns the Recoder-equivalent to a given ModelElement (KeY).
     * If there's no Recoder-equivalent to the ModelElement pe a
     * debug message "Model Element <pe> not known" is printed.
     *
     * @param pe a ModelElement
     */
    public Node toRecoder(ModelElement pe) {
        Node res = revMap.get(pe);
        Debug.assertTrue(res != null, "Model Element not known", pe);

        return res;
    }

    public void put(Node rec, ModelElement key) {
        Object formerValue = map.put(rec, key);
        Debug.assertTrue(formerValue == null,
                "keyrecodermapping: duplicate registration of type:", key);
        revMap.put(key, rec);
        LOGGER.warn("Size of rec2key: {} entries", map.size());
    }

    public boolean mapped(Object rec) {
        return map.containsKey(rec);
    }


    public Set<ModelElement> elemsKeY() {
        LOGGER.error("Size of rec2key: {} entries", map.size());
        return revMap.keySet();
    }

    public Set<Node> elemsRec() {
        return map.keySet();
    }

    public void setSuperArrayType(KeYJavaType superArrayType) {
        this.superArrayType = superArrayType;
    }

    public KeYJavaType getSuperArrayType() {
        return this.superArrayType;
    }

    public KeyJPMapping copy() {
        return new KeyJPMapping(new HashMap<>(map), new HashMap<>(revMap), superArrayType, parsedSpecial);
    }

    /**
     * As long as we do not support lemmata we need the source code of
     * some 'java.lang' classes. These are parsed in using method
     * parseSpecial of {@link Recoder2KeY}. To avoid multiple readings
     * this method indicates whether the special have been parsed in or
     * not.
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
     * As long as we do not support lemmata we need the source code of
     * some 'java.lang' classes. These are parsed in using method
     * parseSpecial of {@link Recoder2KeY}. To avoid multiple readings
     * this method sets a flag whether the special have been parsed in or
     * not
     *
     * @param b boolean indicating if the special classes have been
     *          parsed in
     */
    public void parsedSpecial(boolean b) {
        parsedSpecial = b;
    }
}
