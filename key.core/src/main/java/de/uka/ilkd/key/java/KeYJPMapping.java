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
    private final Map<Node, Object> map;

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
        this.map = new IdentityHashMap<>(4096);
        this.typeMap = new LinkedHashMap<>(4096);
        this.revMap = new IdentityHashMap<>(4096);
    }


    /**
     * creates a KeYRecoderMapping object.
     * Used for cloning and testing.
     *
     * @param o what to clone
     */
    KeYJPMapping(KeYJPMapping o) {
        this.map = new LinkedHashMap<>(o.map);
        this.typeMap = new LinkedHashMap<>(o.typeMap);
        this.revMap = new LinkedHashMap<>(o.revMap);
        this.superArrayType = o.superArrayType;
        this.parsedSpecial = o.parsedSpecial;
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    public Object typeToKeY(Node pe) {
        return map.get(pe);
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    public Optional<KeYJavaType> resolvedTypeToKeY(ResolvedType pe) {
        return Optional.ofNullable(typeMap.get(pe));
    }

    public ResolvedType resolveType(KeYJavaType pe) {
        var res = typeMapRev.get(pe);
        Debug.assertTrue(res != null, "Model Element not known", pe);
        return res;
    }

    public Optional<Object> nodeToKeY(Node rm) {
        return Optional.ofNullable(map.get(rm));
    }

    public Optional<Object> resolvedDeclarationToKeY(ResolvedDeclaration rm) {
        return rm.toAst().flatMap(this::nodeToKeY);
    }

    public void put(Node node, Object value) {
        Object formerValue = map.putIfAbsent(node, value);
        var formerNode = revMap.putIfAbsent(value, node);
        if (formerValue != null && formerValue != value)
            LOGGER.error("Duplicate registration of value: {}, formerValue: {}", value,
                formerValue);
        if (formerNode != null && formerNode != node)
            LOGGER.error("Duplicate registration of node: {}, formerNode: {}", node, formerNode);
    }

    public void put(ResolvedType rec, KeYJavaType key) {
        var formerValue = typeMap.putIfAbsent(rec, key);
        if (formerValue != null && !Objects.equals(formerValue, key))
            LOGGER.error("Duplicate registration of kjt: {}, former kjt: {}", key, formerValue);
        var formerType = typeMapRev.putIfAbsent(key, rec);
        if (formerType != null && !Objects.equals(rec, formerType))
            LOGGER.error("Duplicate registration of resolved type: {}, former: {}", rec,
                formerType);
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
        return new KeYJPMapping(this);
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
}
