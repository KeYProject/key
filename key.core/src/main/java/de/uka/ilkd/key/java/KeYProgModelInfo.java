/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uka.ilkd.key.java.ast.ResolvedLogicalType;
import de.uka.ilkd.key.java.ast.abstraction.ArrayType;
import de.uka.ilkd.key.java.ast.abstraction.Field;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.loader.JP2KeYTypeConverter;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.MethodResolutionCapability;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.DefaultConstructorDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class KeYProgModelInfo {

    private static final Logger LOGGER = LoggerFactory.getLogger(KeYProgModelInfo.class);

    private final KeYJPMapping mapping;
    private final JP2KeYTypeConverter typeConverter;
    private final Map<KeYJavaType, Map<String, IProgramMethod>> implicits = new LinkedHashMap<>();

    public KeYProgModelInfo(JavaService service) {
        this.typeConverter = service.getTypeConverter();
        this.mapping = service.getMapping();
    }

    public KeYJPMapping rec2key() {
        return mapping;
    }

    /**
     * Returns all KeY-elements mapped by Recoder2KeY object of this
     * KeYProgModelInfo.
     *
     * @return a Set object containing the KeY-elements.
     */
    // TODO javaparser Check usages: Does not contain KeYJavaType
    public Set<Object> allElements() {
        return rec2key().elemsKeY();
    }

    /**
     * Returns all KeY-elements mapped by Recoder2KeY object of this
     * KeYProgModelInfo.
     *
     * @return a Set object containing the KeY-elements.
     */

    public Collection<KeYJavaType> allTypes() {
        return rec2key().keYTypes();
    }

    @NonNull
    private List<ResolvedMethodDeclaration> getAllMethods(KeYJavaType kjt) {
        var type = rec2key().resolveType(kjt);
        if (type.isReferenceType()) {
            return type.asReferenceType().getAllMethods();
        }
        return Collections.emptyList();
    }

    /**
     * Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     *
     * @return the list of visible methods of this type and its supertypes.
     */
    public List<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        var methods = getAllMethods(kjt);
        List<IProgramMethod> result = new ArrayList<>(methods.size());
        for (var rm : methods) {
            var declaration = rec2key().resolvedDeclarationToKeY(rm);
            if (declaration != null) {
                result.add((IProgramMethod) declaration);
            }
        }
        return result;
    }

    public KeYJavaType resolveType(String shortName, KeYJavaType context) {
        var type = new ClassOrInterfaceType(null, shortName);
        var rt = getCompilationUnit(context).orElseThrow();
        try {
            type.setParentNode(rt);
            var rtype = type.resolve();
            return typeConverter.getKeYJavaType(rtype);
        } finally {
            rt.remove(type);
        }
    }

    private Optional<CompilationUnit> getCompilationUnit(KeYJavaType kjt) {
        return getReferenceType(kjt)
                .flatMap(ResolvedReferenceType::getTypeDeclaration)
                .flatMap(AssociableToAST::toAst)
                .flatMap(Node::findCompilationUnit);
    }

    /**
     * Returns the full name of a KeYJavaType t.
     *
     * @return the full name of t as a String.
     */
    public String getFullName(KeYJavaType t) {
        var rt = rec2key().resolveType(t);
        if (rt.isReferenceType())
            return rt.asReferenceType().getQualifiedName();
        return rt.describe();
    }

    public boolean isFinal(KeYJavaType kjt) {
        var type = rec2key().resolveType(kjt);
        if (type.isArray() || type.isPrimitive() || type.isVoid() || type.isNull()) {
            return false;
        }
        if (type.isReferenceType()) { // TODO weigl enum declarations and records!
            var rt = type.asReferenceType();
            var td = rt.getTypeDeclaration().orElseThrow();
            if (td.isClass()) {
                var node = (NodeWithModifiers<?>) td.asClass().toAst().get();
                return node.hasModifier(Modifier.Keyword.FINAL);
            }
            if (td.isInterface()) {
                // Interfaces can't be final
                return false;
            }
            if (td instanceof ResolvedLogicalType) {
                // Logic types are not final? Just following primitive types here
                return false;
            }
        }
        throw new UnsupportedOperationException("Type " + type.getClass() + " is not supported");
    }

    /**
     * Checks whether subType is a subtype of superType or not.
     *
     * @return true if subType is subtype of superType,
     *         false in the other case.
     */
    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        return isSubtype(rec2key().resolveType(subType), rec2key().resolveType(superType));
    }

    private boolean isSubtype(ResolvedType subType, ResolvedType superType) {
        return superType.isAssignableBy(subType); // TODO weigl check if it is the right method and
        // order.
    }

    public boolean isPackage(String name) {
        return mapping.isPackageName(name);
    }

    private List<ResolvedConstructorDeclaration> getDeclaredConstructors(KeYJavaType ct) {
        return getReferenceType(ct)
                .flatMap(ResolvedReferenceType::getTypeDeclaration)
                .map(ResolvedReferenceTypeDeclaration::getConstructors)
                .orElseGet(ArrayList::new);
    }

    private ResolvedType getJavaParserType(KeYJavaType ct) {
        return rec2key().resolveType(ct);
    }

    private Optional<ResolvedReferenceType> getReferenceType(KeYJavaType ct) {
        var type = rec2key().resolveType(ct);
        return type.isReferenceType() ? Optional.of(type.asReferenceType()) : Optional.empty();
    }

    /**
     * Returns the ProgramMethods locally defined within the given
     * class type.
     *
     * @param ct a class type.
     */
    public List<ProgramMethod> getAllProgramMethodsLocallyDeclared(KeYJavaType ct) {
        var result = new ArrayList<ProgramMethod>();
        var type = getJavaParserType(ct);
        if (!type.isReferenceType()) {
            return result;
        }
        var rml = type.asReferenceType().getDeclaredMethods();
        result.ensureCapacity(rml.size());
        for (MethodUsage methodUsage : rml) {
            if (methodUsage.getDeclaration() instanceof JavaParserMethodDeclaration) {
                var element = mapping.resolvedDeclarationToKeY(methodUsage.getDeclaration());
                if (element != null) {
                    result.add((ProgramMethod) element);
                }
            }
        }
        return result;
    }

    /**
     * Returns the constructors locally defined within the given
     * class type. If the type is represented in source code,
     * the returned list matches the syntactic order.
     *
     * @param ct a class type.
     */

    public List<IProgramMethod> getConstructors(KeYJavaType ct) {
        var rcl = getDeclaredConstructors(ct);
        var result = new ArrayList<IProgramMethod>(rcl.size());
        for (ResolvedConstructorDeclaration decl : rcl) {
            if (decl instanceof DefaultConstructorDeclaration) {
                // TODO javaparser this node is only returned by
                // ResolvedReferenceTypeDeclaration::getConstructors
                // and neither implements hashCode nor equals
                continue;
            }
            var m = mapping.resolvedDeclarationToKeY(decl);
            if (m != null) {
                result.add((IProgramMethod) m);
            }
        }
        return result;
    }

    /**
     * retrieves the most specific constructor declared in the given type with
     * respect to the given signature
     *
     * @param ct the KeYJavyType where to look for the constructor
     * @param signature IList<KeYJavaType> representing the signature of the constructor
     * @return the most specific constructor declared in the given type
     */
    @Nullable
    public IProgramMethod getConstructor(KeYJavaType ct, ImmutableList<KeYJavaType> signature) {
        var rt = getJavaParserType(ct).asReferenceType().getTypeDeclaration();
        if (rt.isPresent()) {
            List<ResolvedType> sig = signature.stream().map(this::getJavaParserType).toList();

            List<ResolvedConstructorDeclaration> constructors = rt.get().getConstructors();
            constr: for (var constructor : constructors) {
                if (sig.size() != constructor.getNumberOfParams()) {
                    continue;
                }

                if (sig.isEmpty()) { // fast track for default constructor calls!
                    var ast = constructor.toAst().get();
                    return (IProgramMethod) mapping.nodeToKeY(ast);
                }

                // compare types of the parameters
                List<ResolvedType> types = constructor.formalParameterTypes();
                for (int i = 0; i < types.size(); i++) {
                    if (!types.get(i).equals(sig.get(i))) {
                        break constr;
                    }
                }
                var ast = constructor.toAst().get();
                return (IProgramMethod) mapping.nodeToKeY(ast);
            }
            // ((ClassOrInterfaceDeclaration)
            // rt.get().toAst().get()).getConstructorByParameterTypes()
        }
        return null;
    }

    /**
     * retrieves implicit methods
     */
    private IProgramMethod getImplicitMethod(KeYJavaType ct, String name) {
        final Map<String, IProgramMethod> m = implicits.get(ct);
        if (m != null) {
            final IProgramMethod pm = m.get(name);
            if (pm != null) {
                return pm;
            }
        }
        TypeDeclaration cd = (TypeDeclaration) ct.getJavaType();
        ImmutableArray<MemberDeclaration> members = cd.getMembers();
        for (int i = 0; i < members.size(); i++) {
            final MemberDeclaration member = members.get(i);
            if (member instanceof IProgramMethod pm
                    && pm.getMethodDeclaration().getName().equals(name)) {
                return pm;
            }
        }
        LOGGER.debug("keyprogmodelinfo: implicit method {} not found in {}", name, ct);
        return null;
    }

    /**
     * Returns the IProgramMethods with the given name that is defined
     * in the given type or in a supertype where it is visible for the
     * given type, and has a signature that is compatible to the given one.
     *
     * @param ct the class type to get methods from.
     * @param name the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the IProgramMethods, if one is found,
     *         null if none or more than one IProgramMethod is found (in this case
     *         a debug output is written to console).
     */
    @Nullable
    public IProgramMethod getProgramMethod(@NonNull KeYJavaType ct, String name,
            Iterable<KeYJavaType> signature) {
        if (ct.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, name);
        }

        var type = getJavaParserType(ct);
        if (!type.isReferenceType()) {
            return null;
        }
        var rct = type.asReferenceType().getTypeDeclaration().orElseThrow();
        List<ResolvedType> jpSignature = StreamSupport.stream(signature.spliterator(), false)
                .map(this::getJavaParserType).toList();
        var method = MethodResolutionLogic.solveMethodInType(rct, name, jpSignature);

        if (!method.isSolved())
            return null;

        return method.getDeclaration()
                .map(d -> (IProgramMethod) Objects
                        .requireNonNull(mapping.resolvedDeclarationToKeY(d)))
                .orElse(null);
    }

    /**
     * Returns the IProgramMethods with the given name that is defined
     * in the given type or in a supertype where it is visible for the
     * given type, and has a signature that is compatible to the given one.
     *
     * @param ct the class type to get methods from.
     * @param name the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the IProgramMethods, if one is found,
     *         null if none or more than one IProgramMethod is found (in this case
     *         a debug output is written to console).
     */
    public IProgramMethod getProgramMethod(
            @NonNull KeYJavaType ct, String name,
            Iterable<KeYJavaType> signature, KeYJavaType context) {
        // TODO javaparser implement resolution with context
        return getProgramMethod(ct, name, signature);
    }

    private List<Field> asKeYFieldsR(Stream<ResolvedFieldDeclaration> rfl) {
        return rfl.flatMap(
            it -> ((FieldDeclaration) Objects.requireNonNull(mapping.resolvedDeclarationToKeY(it)))
                    .getFieldSpecifications().stream())
                .collect(Collectors.toList());
    }

    /**
     * returns the fields defined within the given class type.
     * If the type is represented in source code, the returned list
     * matches the syntactic order.
     *
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public List<Field> getAllFieldsLocallyDeclaredIn(KeYJavaType ct) {
        if (ct.getJavaType() instanceof ArrayType) {
            return getVisibleArrayFields(ct);
        }
        return getReferenceType(ct)
                .map(r -> asKeYFieldsR(r.getDeclaredFields().stream()))
                .orElseGet(ArrayList::new);
    }


    /**
     * returns all in <tt>ct</tt> visible fields
     * declared in <tt>ct</tt> or one of its supertypes
     * in topological order starting with the fields of
     * the given type
     * If the type is represented in source code, the returned list
     * matches the syntactic order.
     *
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public List<Field> getAllVisibleFields(KeYJavaType ct) {
        if (ct.getJavaType() instanceof ArrayDeclaration) {
            return getVisibleArrayFields(ct);
        }
        // TODO javaparser this should be declared + visible to inheritors of super
        return getReferenceType(ct)
                .map(r -> asKeYFieldsR(r.getDeclaredFields().stream()))
                .orElseGet(ArrayList::new);
    }

    /**
     * returns all fields of and visible in an array field
     *
     * @param arrayType the KeYJavaType of the array
     * @return the list of visible fields
     */
    private List<Field> getVisibleArrayFields(KeYJavaType arrayType) {
        final ImmutableArray<MemberDeclaration> members =
            ((ArrayDeclaration) arrayType.getJavaType()).getMembers();
        List<Field> result = new ArrayList<>();
        for (MemberDeclaration member : members) {
            if (member instanceof FieldDeclaration) {
                final ImmutableArray<FieldSpecification> specs =
                    ((FieldDeclaration) member).getFieldSpecifications();
                for (FieldSpecification spec : specs) {
                    result.add(spec);
                }
            }
        }

        // fields of java.lang.Object visible in an array
        var kjt = typeConverter.getObjectType();
        var objectFields = getReferenceType(kjt)
                .orElseThrow()
                .getDeclaredFields()
                .stream()
                .filter(f -> f.accessSpecifier() != AccessSpecifier.PRIVATE)
                .map(f -> (Field) Objects.requireNonNull(mapping.resolvedDeclarationToKeY(f)))
                .toList();
        result.addAll(objectFields);
        return result;
    }

    /**
     * returns all proper subtypes of class <code>ct</code> (i.e. without <code>ct</code> itself)
     */
    private List<ResolvedReferenceTypeDeclaration> getAllRecoderSubtypes(KeYJavaType ct) {
        final ResolvedType rt = getJavaParserType(ct);
        // TODO javaparser get all known java types in classpath
        // best approximation is to use the recoder2key mapping

        List<Node> types = rec2key().elemsRec().stream()
                .filter(it -> it instanceof com.github.javaparser.ast.body.TypeDeclaration)
                .toList();

        List<ResolvedReferenceTypeDeclaration> res = new ArrayList<>(1024);
        for (var decl : types) {
            ResolvedReferenceTypeDeclaration resolved =
                ((com.github.javaparser.ast.body.TypeDeclaration) decl).resolve();
            if (resolved.canBeAssignedTo(rt.asReferenceType().getTypeDeclaration().get())) // TODO
                                                                                           // weigl
                                                                                           // correct
                                                                                           // direction?
            {
                res.add(resolved);
            }
        }
        // TODO weigl
        return res;
    }

    /**
     * returns all supertypes of the given class type with the type itself as
     * first element
     */
    private List<ResolvedReferenceType> getAllDeclaredSupertypes(KeYJavaType ct) {
        return getReferenceType(ct)
                .map(r -> {
                    var ancestors = r.getAllAncestors();
                    List<ResolvedReferenceType> res = new ArrayList<>(ancestors.size() + 1);
                    res.add(r);
                    res.addAll(ancestors);
                    return res;
                })
                .orElse(Collections.emptyList());
    }


    /**
     * returns a list of KeYJavaTypes representing the given recoder types in
     * the same order
     *
     * @param rctl the ASTList<ClassType> to be converted
     * @return list of KeYJavaTypes representing the given recoder types in
     *         the same order
     */
    private List<KeYJavaType> asKeYJavaTypes(
            final Stream<ResolvedReferenceTypeDeclaration> rctl) {
        return rctl
                .map(it -> Objects
                        .requireNonNull(rec2key().resolvedTypeToKeY(new ReferenceTypeImpl(it))))
                .collect(Collectors.toList());
    }

    /**
     * Returns all known supertypes of the given class type with the type itself
     * as first element.
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public List<KeYJavaType> getAllSupertypes(KeYJavaType ct) {
        final var superTypes = getAllDeclaredSupertypes(ct)
                .stream().map(ResolvedReferenceType::asReferenceType)
                .filter(it -> it.getTypeDeclaration().isPresent())
                .map(it -> it.getTypeDeclaration().get());

        return asKeYJavaTypes(superTypes);
    }

    /**
     * Returns all proper subtypes of the given class type
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public List<KeYJavaType> getAllSubtypes(KeYJavaType ct) {
        return asKeYJavaTypes(getAllRecoderSubtypes(ct).stream());
    }

    /// Returns all {@link KeYJavaType},
    /// ```
    /// for all loaded type declarations td
    /// if td <: ct and implements method with name
    /// add to the returning list
    /// endif
    /// endfor
    /// ```
    public ImmutableList<KeYJavaType> findImplementations(KeYJavaType ct, String name,
            ImmutableList<KeYJavaType> signature) {

        var type = rec2key().resolveType(ct);

        // only reference types has overridable methods
        if (!type.isReferenceType()) {
            return ImmutableList.of();
        }

        var rct = type.asReferenceType().getTypeDeclaration().orElseThrow();
        List<ResolvedType> jpSignature = signature.map(this::getJavaParserType).toList();

        // If ct is an interface, but does not declare the method, we
        // need to start the search "upstairs"

        while (rct.toAst(ClassOrInterfaceDeclaration.class).get().isInterface()
                && !isDeclaringInterface(rct, name, jpSignature)) {
            rct = rct.getAncestors().get(1).getTypeDeclaration().orElseThrow();
        }

        ImmutableList<KeYJavaType> classList = ImmutableSLList.nil();
        classList = recFindImplementations(rct, name, jpSignature, classList);

        if (!declaresApplicableMethods(rct, name, jpSignature)) {
            // ct has no implementation, go up
            List<ResolvedReferenceType> superTypes = rct.getAncestors();
            int k = 0;
            while (k < superTypes.size() && !declaresApplicableMethods(
                superTypes.get(k).getTypeDeclaration().orElseThrow(), name,
                jpSignature))
                k++;
            if (k < superTypes.size()) {
                rct = superTypes.get(k).getTypeDeclaration().orElseThrow();
                KeYJavaType r = (KeYJavaType) mapping.resolvedDeclarationToKeY(rct);
                if (r == null) {
                    LOGGER.info("Type {}", rct.getName());
                } else {
                    classList = classList.append(r);
                }
            } // no implementation is needed if classes above are abstract
        }

        return classList;
    }


    // TODO(weigl): Implemented by @Drodt, no idea if it's correct
    private ImmutableList<KeYJavaType> recFindImplementations(
            ResolvedTypeDeclaration ct,
            String name, List<ResolvedType> signature, ImmutableList<KeYJavaType> result) {
        if (declaresApplicableMethods(ct, name, signature)) {
            var r = typeConverter.getKeYJavaType(ct.getQualifiedName());
            if (r == null) {
                LOGGER.info("Type {}: {} not found", ct.getQualifiedName(), name);
                return result;
            } else if (!result.contains(r)) {
                result = result.prepend(r);
            }
        }

        List<ResolvedReferenceTypeDeclaration> classes = getAllRecoderSubtypes(result.head());

        // alpha sorting to make order deterministic
        var classesArray = classes.toArray(new ResolvedTypeDeclaration[0]);
        java.util.Arrays.sort(classesArray,
            (o1, o2) -> o2.getQualifiedName().compareTo(o1.getQualifiedName()));

        for (var c : classesArray) {
            if (!c.equals(ct)) {
                result = recFindImplementations(c, name, signature, result);
            }
        }
        return result;
    }


    // TODO(weigl): Implemented by @Drodt, no idea if it's correct
    private boolean declaresApplicableMethods(ResolvedTypeDeclaration rt, String name,
            List<ResolvedType> signature) {
        if (rt instanceof MethodResolutionCapability mrc) {
            var method = mrc.solveMethod(name, signature, false);
            return method.isSolved();
        }
        return false;
    }

    // TODO(weigl): Implemented by @Drodt, no idea if it's correct
    private boolean isDeclaringInterface(
            ResolvedTypeDeclaration ct, String name,
            List<ResolvedType> signature) {
        Debug.assertTrue(ct.isInterface());
        var id = ct.asInterface();
        var set = id.getDeclaredMethods();
        for (var m : set) {
            // TODO: check if m is visible for ct
            if (name.equals(m.getName())
                    && isCompatibleSignature(signature, m.formalParameterTypes()))
                return true;
        }
        return false;
    }

    // TODO(weigl): Implemented by @Drodt, no idea if it's correct
    private boolean isCompatibleSignature(List<ResolvedType> sig1, List<ResolvedType> sig2) {
        int sl1 = sig1.size();
        int sl2 = sig2.size();
        if (sl1 != sl2)
            return false;
        for (int i = 0; i < sl1; ++i) {
            var t1 = sig1.get(i);
            var t2 = sig2.get(i);
            if (!isSubtype(t2, t1))
                return false;
        }
        return true;
    }

    private void putImplicitMethod(IProgramMethod m, KeYJavaType t) {
        Map<String, IProgramMethod> map = implicits.computeIfAbsent(t, k -> new LinkedHashMap<>());
        map.put(m.name().toString(), m);
    }
}
