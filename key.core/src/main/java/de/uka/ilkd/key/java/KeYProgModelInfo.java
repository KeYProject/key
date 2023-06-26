package de.uka.ilkd.key.java;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.MethodResolutionCapability;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.DefaultConstructorDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class KeYProgModelInfo {

    private static final Logger LOGGER = LoggerFactory.getLogger(KeYProgModelInfo.class);

    private final Services services;
    private final KeYJPMapping mapping;
    private final JP2KeYTypeConverter typeConverter;
    private final Map<KeYJavaType, Map<String, IProgramMethod>> implicits = new LinkedHashMap<>();
    // TODO javaparser what is this

    public KeYProgModelInfo(Services services, KeYJPMapping mapping,
            JP2KeYTypeConverter typeConverter) {
        this.services = services;
        this.typeConverter = typeConverter;
        this.mapping = mapping;
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

    @Nonnull
    private List<ResolvedMethodDeclaration> getAllRecoderMethods(KeYJavaType kjt) {
        if (kjt.getJavaType() instanceof TypeDeclaration) {
            // TODO javaparser this does not work, type map
            var rtype = rec2key().resolveType(kjt).asReferenceType();
            return rtype.getAllMethods();
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
    public ImmutableList<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        var methods = getAllRecoderMethods(kjt);
        ImmutableList<IProgramMethod> result = ImmutableSLList.nil();
        for (var rm : methods) {
            var declaration = rec2key().resolvedDeclarationToKeY(rm);
            if (declaration.isPresent()) {
                result = result.prepend((IProgramMethod) declaration.get());
            }
        }
        return result;
    }

    public KeYJavaType resolveType(String shortName, KeYJavaType context) {
        var type = new ClassOrInterfaceType(null, shortName);
        var rt = getCompilationUnit(context).orElseThrow();
        type.setParentNode(rt);
        var rtype = type.resolve();
        return typeConverter.getKeYJavaType(rtype);
    }

    private Optional<CompilationUnit> getCompilationUnit(KeYJavaType kjt) {
        return getReferenceType(kjt)
                .flatMap(ResolvedReferenceType::getTypeDeclaration)
                .flatMap(AssociableToAST::toAst)
                .flatMap(Node::findCompilationUnit);
    }

    private <T extends com.github.javaparser.ast.type.Type> T searchType(String shortName,
            List<T> types) {
        for (var type : types) {
            if (type.toDescriptor().equals(shortName)) { // TODO weigl getname of type
                return type;
            }
        }
        return null;
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
        return rt.toDescriptor();
    }


    public boolean isFinal(KeYJavaType kjt) {
        var recoderType = rec2key().resolveType(kjt);
        if (recoderType.isReferenceType()) { // TODO weigl enum declarations and records!
            var rt = recoderType.asReferenceType();
            var td = rt.getTypeDeclaration().get();
            var node = (NodeWithModifiers<?>) td.asClass().toAst().get();
            return node.hasModifier(Modifier.Keyword.FINAL);
        } else { // array or primitive type
            return false;
        }
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

        /*
         * if (subType instanceof ClassOrInterfaceType && superType instanceof ClassOrInterfaceType)
         * {
         *
         * return isSubtype((recoder.abstraction.ClassType) subType,
         * (recoder.abstraction.ClassType) superType);
         * } else if (superType instanceof recoder.abstraction.ArrayType &&
         * subType instanceof recoder.abstraction.ArrayType) {
         * return isAssignmentCompatible((recoder.abstraction.ArrayType) subType,
         * (recoder.abstraction.ArrayType) superType);
         * } else if (subType instanceof recoder.abstraction.ArrayType &&
         * superType instanceof recoder.abstraction.ClassType) {
         * return "java.lang.Object".equals(superType.getFullName())
         * || "Object".equals(superType.getName());
         * }
         * // should not occur
         * throw new RuntimeException("Method isSubtype in class KeYProgModelInfo " +
         * "currently only supports two class types or two " +
         * "array type but no mixture!");
         */
    }

    public boolean isPackage(String name) {
        return mapping.isPackageName(name);
    }

    /**
     * checks whether subType is assignment compatible to type according
     * to the rules defined in the java language specification
     */
    private boolean isAssignmentCompatible(ResolvedArrayType subType, ResolvedArrayType type) {
        return subType.isAssignableBy(type);
        /*
         * recoder.abstraction.Type bt1 = subType.getBaseType();
         * recoder.abstraction.Type bt2 = type.getBaseType();
         * if (bt1 instanceof recoder.abstraction.PrimitiveType &&
         * bt2 instanceof recoder.abstraction.PrimitiveType) {
         * return bt1.getFullName().equals(bt2.getFullName());
         * }
         * if (bt1 instanceof recoder.abstraction.ClassType &&
         * bt2 instanceof recoder.abstraction.ClassType)
         * return isSubtype((recoder.abstraction.ClassType) bt1,
         * (recoder.abstraction.ClassType) bt2);
         * if (bt1 instanceof recoder.abstraction.ArrayType &&
         * bt2 instanceof recoder.abstraction.ArrayType)
         * return isAssignmentCompatible((recoder.abstraction.ArrayType) bt1,
         * (recoder.abstraction.ArrayType) bt2);
         * if (bt1 instanceof recoder.abstraction.ClassType &&
         * bt2 instanceof recoder.abstraction.ArrayType)
         * return false;
         * if (bt1 instanceof recoder.abstraction.ArrayType &&
         * bt2 instanceof recoder.abstraction.ClassType) {
         * if (((recoder.abstraction.ClassType) bt2).isInterface()) {
         * return bt2.
         * getFullName().equals("java.lang.Cloneable") ||
         * bt2.
         * getFullName().equals("java.lang.Serializable")
         * ;
         * } else {
         * return bt2.
         * getFullName().equals("java.lang.Object");
         * }
         * }
         * return false;
         */
    }

    private List<ResolvedMethodDeclaration> getMethods(KeYJavaType kjt) {
        var type = getJavaParserType(kjt);
        if (type.isReferenceType()) {
            return type.asReferenceType().getAllMethods();
        }
        return Collections.emptyList();
    }

    private List<ResolvedConstructorDeclaration> getDeclaredConstructors(KeYJavaType ct) {
        return getReferenceType(ct)
                .flatMap(ResolvedReferenceType::getTypeDeclaration)
                .map(ResolvedReferenceTypeDeclaration::getConstructors)
                .orElse(Collections.emptyList());
    }

    private ResolvedType getJavaParserType(KeYJavaType ct) {
        return rec2key().resolveType(ct);
    }

    private Optional<ResolvedReferenceType> getReferenceType(KeYJavaType ct) {
        var type = rec2key().resolveType(ct);
        return type.isReferenceType() ? Optional.of(type.asReferenceType()) : Optional.empty();
    }


    private List<ResolvedConstructorDeclaration> getRecoderConstructors(KeYJavaType ct,
            ImmutableList<KeYJavaType> signature) {
        // var cd = getConstructors(ct);
        // return rct.getProgramModelInfo().getConstructors(rct, getRecoderTypes(signature));
        // return cd;
        // TODO weigl
        throw new UnsupportedOperationException();
    }

    /**
     * Returns the ProgramMethods locally defined within the given
     * class type.
     *
     * @param ct a class type.
     */
    public ImmutableList<ProgramMethod> getAllProgramMethodsLocallyDeclared(KeYJavaType ct) {
        ImmutableList<ProgramMethod> result = ImmutableSLList.nil();
        var type = getJavaParserType(ct);
        if (!type.isReferenceType()) {
            return result;
        }
        var rml = type.asReferenceType().getDeclaredMethods();
        for (MethodUsage methodUsage : rml) {
            if (methodUsage.getDeclaration() instanceof JavaParserMethodDeclaration) {
                var element = mapping.resolvedDeclarationToKeY(methodUsage.getDeclaration());
                if (element.isPresent()) {
                    result = result.prepend((ProgramMethod) element.get());
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

    public ImmutableList<IProgramMethod> getConstructors(KeYJavaType ct) {
        var rcl = getDeclaredConstructors(ct);
        ImmutableList<IProgramMethod> result = ImmutableSLList.nil();
        for (int i = rcl.size() - 1; i >= 0; i--) {
            var rm = rcl.get(i);
            if (rm instanceof DefaultConstructorDeclaration) {
                // TODO javaparser this node is only returned by
                // ResolvedReferenceTypeDeclaration::getConstructors
                // and neither implements hashCode nor equals
                continue;
            }
            var m = mapping.resolvedDeclarationToKeY(rm);
            if (m.isPresent()) {
                result = result.prepend((IProgramMethod) m.get());
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
    public IProgramMethod getConstructor(KeYJavaType ct, ImmutableList<KeYJavaType> signature) {
        throw new UnsupportedOperationException();
        // var constructors = getRecoderConstructors(ct, signature);
        // if (constructors.size() == 1) {
        // return (IProgramMethod) rec2key().toKeY(constructors.get(0)).orElse(null);
        // }
        // if (constructors.isEmpty()) {
        // LOGGER.debug("javainfo: Constructor not found: {}", ct);
        // return null;
        // }
        // Debug.fail();
        // return null;
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
            if (member instanceof IProgramMethod
                    && ((IProgramMethod) member).getMethodDeclaration().getName().equals(name)) {
                return (IProgramMethod) member;
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
    public IProgramMethod getProgramMethod(@Nonnull KeYJavaType ct, String name,
            Iterable<KeYJavaType> signature) {
        if (ct.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, name);
        }

        var type = getJavaParserType(ct);
        var rct = type.asReferenceType().getTypeDeclaration().orElseThrow();
        List<ResolvedType> jpSignature = StreamSupport.stream(signature.spliterator(), false)
                .map(this::getJavaParserType).toList();
        var method = MethodResolutionLogic.solveMethodInType(rct, name, jpSignature);
        return method.getDeclaration()
                .map(d -> (IProgramMethod) mapping.resolvedDeclarationToKeY(d).orElseThrow())
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
            @Nonnull KeYJavaType ct, String name,
            ImmutableList<? extends Type> signature, KeYJavaType context) {
        if (ct.getJavaType() instanceof ArrayType || context.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, name);
        }

        throw new UnsupportedOperationException();
    }


    /**
     * returns the same fields as given in <tt>rfl</tt> and returns
     * their KeY representation
     *
     * @param rfl the List of fields to be looked up
     * @return list with the corresponding fields as KeY datastructures
     */
    private ImmutableList<Field> asKeYFields(
            Collection<com.github.javaparser.ast.body.FieldDeclaration> rfl) {
        ImmutableList<Field> result = ImmutableSLList.nil();
        if (rfl == null) {
            // this occurs for the artificial Null object at the moment
            // should it have implicit fields?
            return result;
        }
        for (var rf : rfl) {
            for (var decl : rf.getVariables()) {
                Field f = (Field) rec2key().typeToKeY(decl);
                if (f != null) {
                    result = result.prepend(f);
                } else {
                    LOGGER.debug("Field has no KeY equivalent (recoder field): {}", rf);
                    LOGGER.debug("This happens currently as classes only available in byte code "
                        + "are only partially converted ");
                }
            }
        }
        return result;
    }

    private ImmutableList<Field> asKeYFieldsR(Stream<ResolvedFieldDeclaration> rfl) {
        return ImmutableList.fromList(rfl
                .flatMap(
                    it -> ((FieldDeclaration) mapping.resolvedDeclarationToKeY(it).orElseThrow())
                            .getFieldSpecifications().stream())
                .collect(Collectors.toList()));
    }

    /**
     * returns the fields defined within the given class type.
     * If the type is represented in source code, the returned list
     * matches the syntactic order.
     *
     * @param ct the class type whose fields are returned
     * @return the list of field members of the given type.
     */
    public ImmutableList<Field> getAllFieldsLocallyDeclaredIn(KeYJavaType ct) {
        if (ct.getJavaType() instanceof ArrayType) {
            return getVisibleArrayFields(ct);
        }
        return getReferenceType(ct)
                .map(r -> asKeYFieldsR(r.getDeclaredFields().stream()))
                .orElse(ImmutableSLList.nil());
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
    public ImmutableList<Field> getAllVisibleFields(KeYJavaType ct) {
        if (ct.getJavaType() instanceof ArrayDeclaration) {
            return getVisibleArrayFields(ct);
        }
        // TODO javaparser this should be declared + visible to inheritors of super
        return getReferenceType(ct)
                .map(r -> asKeYFieldsR(r.getDeclaredFields().stream()))
                .orElse(ImmutableSLList.nil());
    }

    /**
     * returns all fields of and visible in an array field
     *
     * @param arrayType the KeYJavaType of the array
     * @return the list of visible fields
     */
    private ImmutableList<Field> getVisibleArrayFields(KeYJavaType arrayType) {
        ImmutableList<Field> result = ImmutableSLList.nil();

        final ImmutableArray<MemberDeclaration> members =
            ((ArrayDeclaration) arrayType.getJavaType()).getMembers();

        for (int i = members.size() - 1; i >= 0; i--) {
            final MemberDeclaration member = members.get(i);
            if (member instanceof FieldDeclaration) {
                final ImmutableArray<FieldSpecification> specs =
                    ((FieldDeclaration) member).getFieldSpecifications();
                for (int j = specs.size() - 1; j >= 0; j--) {
                    result = result.prepend(specs.get(j));
                }
            }
        }

        // fields of java.lang.Object visible in an array
        var obj =
            new ReferenceTypeImpl(services.getJavaService().getProgramFactory().getTypeSolver()
                    .getSolvedJavaLangObject());
        var kjt = rec2key().resolvedTypeToKeY(obj).orElseThrow();
        return getReferenceType(kjt)
                .map(r -> ImmutableList.fromList(r.getDeclaredFields()
                        .stream()
                        .filter(f -> f.accessSpecifier() != AccessSpecifier.PRIVATE)
                        .map(f -> (Field) mapping.resolvedDeclarationToKeY(f).orElseThrow())
                        .toList()))
                .orElse(ImmutableSLList.nil());
    }

    /**
     * returns all proper subtypes of class <code>ct</code> (i.e. without <code>ct</code> itself)
     */
    private List<ResolvedReferenceTypeDeclaration> getAllRecoderSubtypes(KeYJavaType ct) {
        var rt = getJavaParserType(ct);
        // TODO javaparser get all known java types in classpath
        // best approximation is to use the recoder2key mapping

        var types = rec2key().elemsRec().stream()
                .filter(it -> it instanceof ResolvedReferenceTypeDeclaration)
                .toList();

        List<ResolvedReferenceTypeDeclaration> res = new ArrayList<>(1024);
        for (var decl : types) {
            ResolvedReferenceTypeDeclaration resolved = (ResolvedReferenceTypeDeclaration) decl;
            if (resolved.isAssignableBy(rt)) // TODO weigl correct direction?
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
    private ImmutableList<KeYJavaType> asKeYJavaTypes(
            final List<ResolvedReferenceTypeDeclaration> rctl) {
        return rctl.stream()
                .map(it -> rec2key().resolvedTypeToKeY(new ReferenceTypeImpl(it)).orElseThrow())
                .collect(ImmutableList.collector());
    }

    /**
     * Returns all known supertypes of the given class type with the type itself
     * as first element.
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType ct) {
        final var superTypes = getAllDeclaredSupertypes(ct)
                .stream().map(ResolvedReferenceType::asReferenceType)
                .filter(it -> it.getTypeDeclaration().isPresent())
                .map(it -> it.getTypeDeclaration().get())
                .collect(Collectors.toList());

        return asKeYJavaTypes(superTypes);
    }

    /**
     * Returns all proper subtypes of the given class type
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSubtypes(KeYJavaType ct) {
        return asKeYJavaTypes(getAllRecoderSubtypes(ct));
    }

    public ImmutableList<KeYJavaType> findImplementations(KeYJavaType ct, String name,
            ImmutableList<KeYJavaType> signature) {
        var type = rec2key().resolveType(ct);
        var rct = type.asReferenceType().getTypeDeclaration().orElseThrow();
        List<ResolvedType> jpSignature = signature.map(this::getJavaParserType).toList();
        var method = MethodResolutionLogic.solveMethodInType(rct, name, jpSignature);
        // TODO javaparser

        // If ct is an interface, but does not declare the method, we
        // need to start the search "upstairs"
        // while (rct.toAst(ClassOrInterfaceDeclaration.class).get().isInterface()
        // && !isDeclaringInterface(rct, name, rsignature)) {
        // rct = rct.getAllSupertypes().get(1);
        // }
        //
        ImmutableList<KeYJavaType> classList = ImmutableSLList.nil();
        // classList = recFindImplementations(rct, name, rsignature, classList);
        //
        //
        // if (!declaresApplicableMethods(rct, name, rsignature)) {
        // // ct has no implementation, go up
        // List<recoder.abstraction.ClassType> superTypes = rct.getAllSupertypes();
        // int k = 0;
        // while (k < superTypes.size() && !declaresApplicableMethods(superTypes.get(k), name,
        // rsignature)) k++;
        // if (k < superTypes.size()) {
        // rct = superTypes.get(k);
        // KeYJavaType r = (KeYJavaType) mapping.toKeY(rct);
        // if (r == null) {
        // LOGGER.info("Type {}", rct.getName());
        // } else {
        // classList = classList.append(r);
        // }
        // } // no implementation is needed if classes above are abstract
        // }

        return classList;
    }


    private ImmutableList<KeYJavaType> recFindImplementations(TypeDeclaration ct,
            String name, List<Type> signature, ImmutableList<KeYJavaType> result) {
        // TODO weigl does not compile, no idea what this should be
        // if (declaresApplicableMethods(ct, name, signature)) {
        // KeYJavaType r = (KeYJavaType) mapping.toKeY(ct);
        // if (r == null) {
        // LOGGER.info("Type {}: {} not found", ct.getFullName(), name);
        // } else if (!result.contains(r)) {
        // result = result.prepend(r);
        // }
        // }
        //
        // List<recoder.abstraction.ClassType> classes = si.getSubtypes(ct);
        //
        // //alpha sorting to make order deterministic
        // recoder.abstraction.ClassType[] classesArray = classes.toArray(new ClassType[0]);
        // java.util.Arrays.sort(classesArray, (o1, o2) ->
        // o2.getFullName().compareTo(o1.getFullName()));
        //
        // for (recoder.abstraction.ClassType c : classesArray) {
        // result = recFindImplementations(c, name, signature, result);
        // }
        // return result;
        return null;
    }


    private boolean declaresApplicableMethods(MethodResolutionCapability ct, String name,
            List<ResolvedType> signature) {
        var method = ct.solveMethod(name, signature, false);
        return method.isSolved();
    }

    private boolean isDeclaringInterface(/*
                                          * recoder.abstraction.ClassType ct, String name,
                                          * List<recoder.abstraction.Type> signature
                                          */) {
        // TODO Weigl does not compile
        // Debug.assertTrue(ct.isInterface());
        // List<recoder.abstraction.Method> list = si.getMethods(ct);
        // int s = list.size();
        // int i = 0;
        // while (i < s) {
        // recoder.abstraction.Method m = list.get(i);
        // if (name.equals(m.getName()) && si.isCompatibleSignature(signature, m.getSignature()) &&
        // si.isVisibleFor(m, ct))
        // return true;
        // else i++;
        // }
        return false;
    }

    private void putImplicitMethod(IProgramMethod m, KeYJavaType t) {
        Map<String, IProgramMethod> map = implicits.computeIfAbsent(t, k -> new LinkedHashMap<>());
        map.put(m.name().toString(), m);
    }


    public KeYProgModelInfo copy() {
        return new KeYProgModelInfo(services, rec2key().copy(), typeConverter);
    }
}
