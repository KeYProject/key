/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.*;

import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.util.Debug;

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
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
     * are we currently parsing library classes
     */
    private boolean parsingLibraries = false;

    /**
     * maps a recoder programelement (or something similar, e.g. Type)
     * to the KeY-equivalent
     */
    private final Map<Node, ProgramElement> map;

    /**
     * maps a recoder programelement (or something similar, e.g. Type)
     * to the KeY-equivalent
     */
    private final HashMap<ResolvedType, KeYJavaType> typeMap;
    private final Map<KeYJavaType, ResolvedType> typeMapRev;

    /**
     * maps a KeY programelement to the Recoder-equivalent
     */
    private final Map<ProgramElement, Node> revMap;

    /**
     * a pseudo super class for all arrays used to declare length
     */
    private KeYJavaType superArrayType = null;

    private final Set<String> packageNames;

    private final JavaService converter;

    public KeYJPMapping(JavaService converter) {
        this.converter = converter;

        this.map = new IdentityHashMap<>(4096);
        this.revMap = new IdentityHashMap<>(4096);
        this.typeMap = new LinkedHashMap<>(4096);
        this.typeMapRev = new LinkedHashMap<>(4096);
        this.packageNames = new LinkedHashSet<>(4096);
    }


    /**
     * creates a KeYRecoderMapping object.
     * Used for cloning and testing.
     *
     * @param o what to clone
     */
    KeYJPMapping(KeYJPMapping o) {
        this.map = new IdentityHashMap<>(o.map);
        this.revMap = new IdentityHashMap<>(o.revMap);
        this.typeMap = new LinkedHashMap<>(o.typeMap);
        this.typeMapRev = new LinkedHashMap<>(o.typeMapRev);
        this.packageNames = new LinkedHashSet<>(o.packageNames);
        this.superArrayType = o.superArrayType;
        this.parsedSpecial = o.parsedSpecial;
        this.parsingLibraries = o.parsingLibraries;
        this.converter = o.converter;
    }

    public KeYJavaType resolvedTypeToKeY(ResolvedType pe) {
        return resolvedTypeToKeY(pe, false);
    }

    /**
     * returns a matching ModelElement (KeY) to a given recoder.ModelElement
     *
     * @param pe a recoder.ModelElement
     */
    @Nullable
    public KeYJavaType resolvedTypeToKeY(ResolvedType pe, boolean processOnDemand) {
        var type = typeMap.get(pe);

        if (processOnDemand && type == null && pe.isReferenceType()) {
            try {
                pe.asReferenceType()
                        .getTypeDeclaration()
                        .flatMap(AssociableToAST::toAst)
                        .ifPresent(converter.getConverter(null)::process);
            } catch (ClassCastException e) {
                // This class does not exist
            }
        }
        return type;
    }

    public JavaService getJavaServices() {
        return converter;
    }

    public ResolvedType resolveType(KeYJavaType pe) {
        var res = typeMapRev.get(pe);
        Debug.assertTrue(res != null, "Model Element not known", pe);
        return res;
    }

    @Nullable
    public ProgramElement nodeToKeY(Node rm) {
        return map.get(rm);
    }

    @Nullable
    public ProgramElement resolvedDeclarationToKeY(ResolvedDeclaration rm) {
        var ast = rm.toAst();
        return ast.map(this::nodeToKeY).orElse(null);
    }

    @Nullable
    public Node nodeFromKeY(ProgramElement el) {
        return revMap.get(el);
    }

    public void put(Node node, ProgramElement value) {
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
        return Collections.unmodifiableSet(revMap.keySet());
    }

    public Collection<KeYJavaType> keYTypes() {
        return Collections.unmodifiableCollection(this.typeMap.values());
    }

    public Set<Node> elemsRec() {
        return Collections.unmodifiableSet(map.keySet());
    }

    public void setSuperArrayType(KeYJavaType superArrayType) {
        this.superArrayType = superArrayType;
    }

    public KeYJavaType getSuperArrayType() {
        return this.superArrayType;
    }

    public boolean isPackageName(@NonNull String name) {
        return packageNames.contains(name);
    }

    public void registerPackageName(@NonNull String name) {
        int onePastLastDot = 0;
        while (true) {
            int dot = name.indexOf('.', onePastLastDot);
            int end = dot == -1 ? name.length() : dot;
            packageNames.add(name.substring(0, end));
            onePastLastDot = dot + 1;
            if (dot == -1) {
                break;
            }
        }
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
    public boolean setParsedSpecial() {
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
    public void setParsedSpecial(boolean b) {
        parsedSpecial = b;
    }

    public boolean isParsingLibraries() {
        return parsingLibraries;
    }

    public void setParsingLibraries(boolean parsingLibraries) {
        this.parsingLibraries = parsingLibraries;
    }

    public void registerType(ResolvedType ref, KeYJavaType kjt) {
        System.out.println("Registered " + ref + "   " + kjt);
        this.typeMap.put(ref, kjt);
        this.typeMapRev.put(kjt, ref);
    }
}
