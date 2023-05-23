package de.uka.ilkd.key.java;

import java.util.*;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.util.Debug;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class KeYJPMapping {
    public static final Logger LOGGER = LoggerFactory.getLogger(KeYJPMapping.class);

    /**
     * have special classes been parsed in
     */
    private boolean parsedSpecial = false;

    /**
     * maps a recoder programelement (or something similar, e.g. Type)
     * to the KeY-equivalent
     */
    private final HashMap<Node, Object> map;

    /**
     * maps a recoder programelement (or something similar, e.g. Type)
     * to the KeY-equivalent
     */
    private final HashMap<ResolvedType, KeYJavaType> typeMap;
    private final Map<KeYJavaType, ResolvedType> typeMapRev = new HashMap<>();

    /**
     * maps a KeY programelement to the Recoder-equivalent
     */
    private final Map<Object, Node> revMap;

    /**
     * a pseudo super class for all arrays used to declare length
     */
    private KeYJavaType superArrayType = null;


    public KeYJPMapping() {
        this.map = new LinkedHashMap<>(4096);
        this.typeMap = new LinkedHashMap<>(4096);
        this.revMap = new LinkedHashMap<>(4096);
    }


    /**
     * creates a KeYRecoderMapping object.
     * Used for cloning and testing.
     *
     * @param map a HashMap mapping ProgramElements in Recoder to
     *        ProgramElements in KeY
     * @param revMap the reverse map (KeY->Recoder)
     * @param parsedSpecial boolean indicating if the special classes have been parsed in
     */
    KeYJPMapping(HashMap<Node, Object> map, HashMap<ResolvedType, KeYJavaType> typeMap,
            Map<Object, Node> revMap,
            KeYJavaType superArrayType,
            boolean parsedSpecial) {
        this.map = map;
        this.typeMap = typeMap;
        this.revMap = revMap;
        this.superArrayType = superArrayType;
        this.parsedSpecial = parsedSpecial;
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    public Object toKeY(Node pe) {
        return map.get(pe);
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    public KeYJavaType toKeY(ResolvedType pe) {
        return typeMap.get(pe);
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
    public Node toRecoder(Object pe) {
        Node res = revMap.get(pe);
        Debug.assertTrue(res != null, "Model Element not known", pe);
        return res;
    }

    public ResolvedType toRecoder(KeYJavaType pe) {
        var res = typeMapRev.get(pe);
        Debug.assertTrue(res != null, "Model Element not known", pe);
        return res;
    }


    public void put(Node rec, Object key) {
        Object formerValue = map.put(rec, key);
        if (formerValue != null)
            LOGGER.error("Duplicate registration of type: {}, formerValue: {}", key, formerValue);
        revMap.put(key, rec);
        // TODO javaparser remove
        LOGGER.warn("Size of rec2key: {} entries", map.size());
    }

    public void put(ResolvedType rec, KeYJavaType key) {
        var formerValue = typeMap.put(rec, key);
        if (formerValue != null)
            LOGGER.error("Duplicate registration of resolved type: {}, formerValue: {}", key,
                formerValue);
        typeMapRev.put(key, rec);
    }

    public boolean mapped(Node rec) {
        return map.containsKey(rec);
    }

    public Set<Object> elemsKeY() {
        return revMap.keySet();
    }

    public Collection<KeYJavaType> keYTypes() {
        return this.typeMap.values();
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

    public KeYJPMapping copy() {
        return new KeYJPMapping(new LinkedHashMap<>(map), new LinkedHashMap<>(typeMap),
            new LinkedHashMap<>(revMap), superArrayType, parsedSpecial);
    }

    /**
     * As long as we do not support lemmata we need the source code of
     * some 'java.lang' classes. These are parsed in using method
     * parseSpecial of {@link JavaService}. To avoid multiple readings
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
     * parseSpecial of {@link JavaService}. To avoid multiple readings
     * this method sets a flag whether the special have been parsed in or
     * not
     *
     * @param b boolean indicating if the special classes have been
     *        parsed in
     */
    public void parsedSpecial(boolean b) {
        parsedSpecial = b;
    }

    public Object toKeY(ResolvedDeclaration rm) {
        // TODO weigl
        return toKeY(rm.toAst().get());
    }
}
