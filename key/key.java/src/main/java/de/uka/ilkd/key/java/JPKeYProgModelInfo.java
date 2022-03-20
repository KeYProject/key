package de.uka.ilkd.key.java;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import java.util.*;
import java.util.stream.Collectors;

public class JPKeYProgModelInfo {
    private static final Logger LOGGER = LoggerFactory.getLogger(JPKeYProgModelInfo.class);

    private final Services services;
    private final KeYJPMapping mapping;
    private final JP2KeYTypeConverter typeConverter;
    private final Map<KeYJavaType, Map<String, IProgramMethod>> implicits = new LinkedHashMap<>();
    private KeYRecoderExcHandler exceptionHandler = null;
    private JavaService javaService;

    public JPKeYProgModelInfo(Services services, KeYJPMapping mapping, JP2KeYTypeConverter typeConverter, KeYRecoderExcHandler keh) {
        exceptionHandler = keh;
        this.services = services;
        this.typeConverter = typeConverter;
        this.mapping = mapping;

    }


    public KeYJPMapping rec2key() {
        return mapping;
    }

    public KeYRecoderExcHandler getExceptionHandler() {
        return exceptionHandler;
    }

    /**
     * Returns all KeY-elements mapped by Recoder2KeY object of this
     * KeYProgModelInfo.
     *
     * @return a Set object containing the KeY-elements.
     */

    public Set<Object> allElements() {
        return rec2key().elemsKeY();
    }

    @Nonnull
    private Set<MethodUsage> getAllRecoderMethods(KeYJavaType kjt) {
        if (kjt.getJavaType() instanceof TypeDeclaration) {
            com.github.javaparser.ast.body.TypeDeclaration<?> o = (com.github.javaparser.ast.body.TypeDeclaration<?>) rec2key().toRecoder(kjt);
            var rtype = o.resolve();
            return rtype.getAllMethods();
        }
        return Collections.emptySet();
    }


    /**
     * Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     *
     * @return the list of visible methods of this type and its supertypes.
     */
    public ImmutableList<Method> getAllMethods(KeYJavaType kjt) {
        var rmethods = getAllRecoderMethods(kjt);
        return rmethods.stream().map(it -> ((IProgramMethod) rec2key().toKeY(it.getDeclaration().toAst().get())).getMethodDeclaration()).collect(ImmutableList.collector());
    }


    /**
     * Returns all visible methods that are defined in this
     * class type or any of its supertypes. The methods are
     * in topological order with respect to the inheritance hierarchy.
     *
     * @return the list of visible methods of this type and its supertypes.
     */
    public ImmutableList<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        var rmethods = getAllRecoderMethods(kjt);
        ImmutableList<IProgramMethod> result = ImmutableSLList.nil();
        for (MethodUsage rm : rmethods) {
            IProgramMethod m = (IProgramMethod) rec2key().toKeY(rm.getDeclaration().toAst().get());
            if (m != null) {
                result = result.prepend(m);
            }
        }
        return result;
    }

    @Nonnull
    private List<Type> getRecoderTypes(ImmutableList<? extends Type> types) {
        if (types == null) {
            return Collections.emptyList();
        }
        return types.stream().map(it -> (Type) rec2key().toRecoder(it)).collect(Collectors.toList());
    }

    public KeYJavaType resolveType(String shortName, KeYJavaType context) {
        var type = new ClassOrInterfaceType(null, shortName);
        var rt = getCompilationUnit(context).get();
        type.setParentNode(rt);
        var rtype = type.resolve();
        return typeConverter.convert(rtype);
    }

    private Optional<CompilationUnit> getCompilationUnit(KeYJavaType kjt) {
        var type = getJPType(kjt);
        var rt = type.asClassOrInterfaceType().resolve();
        var td = rt.asReferenceType().getTypeDeclaration().get();
        var node = td.asClass().toAst().get();
        return node.findCompilationUnit();
    }

    private <T extends com.github.javaparser.ast.type.Type> T searchType(String shortName, List<T> types) {
        for (var type : types) {
            if (type.toDescriptor().equals(shortName)) { //TODO weigl getname of type
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
        var rt = (com.github.javaparser.ast.type.Type) rec2key().toRecoder(t);
        if (rt.isClassOrInterfaceType()) return rt.asClassOrInterfaceType().getNameWithScope();
        return rt.toDescriptor();
    }

    private com.github.javaparser.ast.type.Type getType(TypeReference tr) {
        if (tr instanceof TypeRef) {
            return (com.github.javaparser.ast.type.Type) rec2key().toRecoder(tr.getKeYJavaType());
        }
        return null;
    }


    public boolean isFinal(KeYJavaType kjt) {
        var recoderType = (com.github.javaparser.ast.type.Type) rec2key().toRecoder(kjt);
        if (recoderType.isClassOrInterfaceType()) { //TODO enum declarations and records!
            var rt = recoderType.asClassOrInterfaceType().resolve();
            var td = rt.asReferenceType().getTypeDeclaration().get();
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
     * false in the other case.
     */
    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        return isSubtype((com.github.javaparser.ast.type.Type) rec2key().toRecoder(subType), (com.github.javaparser.ast.type.Type) rec2key().toRecoder(superType));
    }

    private boolean isSubtype(com.github.javaparser.ast.type.Type subType, com.github.javaparser.ast.type.Type superType) {
        var a = subType.resolve();
        var b = superType.resolve();
        return b.isAssignableBy(a); //TODO weigl check if it is the right method and order.

        /*
        if (subType instanceof ClassOrInterfaceType && superType instanceof ClassOrInterfaceType) {

            return isSubtype((recoder.abstraction.ClassType) subType,
                    (recoder.abstraction.ClassType) superType);
        } else if (superType instanceof recoder.abstraction.ArrayType &&
                subType instanceof recoder.abstraction.ArrayType) {
            return isAssignmentCompatible((recoder.abstraction.ArrayType) subType,
                    (recoder.abstraction.ArrayType) superType);
        } else if (subType instanceof recoder.abstraction.ArrayType &&
                superType instanceof recoder.abstraction.ClassType) {
            return "java.lang.Object".equals(superType.getFullName())
                    || "Object".equals(superType.getName());
        }
        // should not occur
        throw new RuntimeException("Method isSubtype in class KeYProgModelInfo " +
                "currently only supports two class types or two " +
                "array type but no mixture!");*/
    }

    /**
     * checks if name refers to a package
     *
     * @param name a String with the name to be checked
     * @return true iff name refers to a package
     */
    public boolean isPackage(String name) {
        return !javaService.getTypeSolver().hasType(name);
    }

    /**
     * checks whether subType is assignment compatible to type according
     * to the rules defined in the java language specification
     */
    private boolean isAssignmentCompatible(ResolvedArrayType subType, ResolvedArrayType type) {
        return subType.isAssignableBy(type);
        /*
        recoder.abstraction.Type bt1 = subType.getBaseType();
        recoder.abstraction.Type bt2 = type.getBaseType();
        if (bt1 instanceof recoder.abstraction.PrimitiveType &&
                bt2 instanceof recoder.abstraction.PrimitiveType) {
            return bt1.getFullName().equals(bt2.getFullName());
        }
        if (bt1 instanceof recoder.abstraction.ClassType &&
                bt2 instanceof recoder.abstraction.ClassType)
            return isSubtype((recoder.abstraction.ClassType) bt1,
                    (recoder.abstraction.ClassType) bt2);
        if (bt1 instanceof recoder.abstraction.ArrayType &&
                bt2 instanceof recoder.abstraction.ArrayType)
            return isAssignmentCompatible((recoder.abstraction.ArrayType) bt1,
                    (recoder.abstraction.ArrayType) bt2);
        if (bt1 instanceof recoder.abstraction.ClassType &&
                bt2 instanceof recoder.abstraction.ArrayType)
            return false;
        if (bt1 instanceof recoder.abstraction.ArrayType &&
                bt2 instanceof recoder.abstraction.ClassType) {
            if (((recoder.abstraction.ClassType) bt2).isInterface()) {
                return bt2.
                        getFullName().equals("java.lang.Cloneable") ||
                        bt2.
                                getFullName().equals("java.lang.Serializable")
                        ;
            } else {
                return bt2.
                        getFullName().equals("java.lang.Object");
            }
        }
        return false;*/
    }

    private List<ResolvedMethodDeclaration> getRecoderMethods(KeYJavaType kjt) {
        com.github.javaparser.ast.type.Type type = (com.github.javaparser.ast.type.Type) rec2key().toRecoder(kjt.getJavaType());
        var rtype = type.resolve();
        if (rtype.isReferenceType()) {
            return rtype.asReferenceType().getAllMethods();
        }
        return Collections.emptyList();
    }

    private List<ConstructorDeclaration> getRecoderConstructors(KeYJavaType ct) {
        var type = getJPType(ct);
        var rtype = type.resolve();
        //TODO return rtype.asReferenceType().;
    }

    private com.github.javaparser.ast.type.Type getJPType(KeYJavaType ct) {
        return (com.github.javaparser.ast.type.Type) rec2key().toRecoder(ct);
    }

    private List<ResolvedMethodDeclaration> getRecoderMethods(KeYJavaType ct, String name, ImmutableList<? extends Type> signature, KeYJavaType context) {
        var rct = getJPType(ct).resolve();
        var rcontext = getJPType(context);

        var methods = rct.asReferenceType().getAllMethods();
        //TODO weigl filter out invisible methods in given context
        return methods;
    }


    private List<ResolvedConstructorDeclaration> getRecoderConstructors(KeYJavaType ct, ImmutableList<KeYJavaType> signature) {
        //var cd = getConstructors(ct);
        //        return rct.getProgramModelInfo().getConstructors(rct, getRecoderTypes(signature));
        //return cd;
    }


    /**
     * Returns the list of most specific methods with the given
     * name that are defined in the given type or in a supertype
     * where they are visible for the given type, and have a signature
     * that is compatible to the given one. If used to resolve a
     * method call, the result should be defined and unambiguous.
     *
     * @param ct        the class type to get methods from.
     * @param m         the name of the methods in question.
     * @param signature the statical type signature of a callee.
     */

    private ImmutableList<Method> getMethods(KeYJavaType ct, String m, ImmutableList<Type> signature, KeYJavaType context) {
        List<recoder.abstraction.Method> rml = getRecoderMethods(ct, m, signature, context);
        ImmutableList<Method> result = ImmutableSLList.nil();
        for (int i = rml.size() - 1; i >= 0; i--) {
            recoder.abstraction.Method rm = rml.get(i);
            Method method = (Method) rec2key().toKeY(rm);
            result = result.prepend(method);
        }
        return result;
    }


    /**
     * Returns the methods locally defined within the given
     * class type. If the type is represented in source code,
     * the returned list matches the syntactic order.
     *
     * @param ct a class type.
     */

    public ImmutableList<Method> getMethods(KeYJavaType ct) {
        List<recoder.abstraction.Method> rml = getRecoderMethods(ct);
        ImmutableList<Method> result = ImmutableSLList.nil();
        for (int i = rml.size() - 1; i >= 0; i--) {
            recoder.abstraction.Method rm = rml.get(i);
            if (!(rm instanceof recoder.bytecode.MethodInfo)) {
                Method m = ((IProgramMethod) rec2key().toKeY(rm)).getMethodDeclaration();
                result = result.prepend(m);
            }
        }
        return result;
    }

    /**
     * Returns the ProgramMethods locally defined within the given
     * class type. If the type is represented in source code,
     * the returned list matches the syntactic order.
     *
     * @param ct a class type.
     */
    public ImmutableList<ProgramMethod> getAllProgramMethodsLocallyDeclared(KeYJavaType ct) {
        List<recoder.abstraction.Method> rml = getRecoderMethods(ct);
        ImmutableList<ProgramMethod> result = ImmutableSLList.nil();
        for (int i = rml.size() - 1; i >= 0; i--) {
            recoder.abstraction.Method rm = rml.get(i);
            if (!(rm instanceof recoder.bytecode.MethodInfo)) {
                final var element = (ProgramMethod) rec2key().toKeY(rm);
                if (element != null) {
                    result = result.prepend(element);
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
        List<? extends Constructor> rcl = getRecoderConstructors(ct);
        ImmutableList<IProgramMethod> result = ImmutableSLList.nil();
        for (int i = rcl.size() - 1; i >= 0; i--) {
            recoder.abstraction.Method rm = rcl.get(i);
            IProgramMethod m = (IProgramMethod) rec2key().toKeY(rm);
            if (m != null) {
                result = result.prepend(m);
            }
        }
        return result;
    }

    /**
     * retrieves the most specific constructor declared in the given type with
     * respect to the given signature
     *
     * @param ct        the KeYJavyType where to look for the constructor
     * @param signature IList<KeYJavaType> representing the signature of the constructor
     * @return the most specific constructor declared in the given type
     */
    public IProgramMethod getConstructor(KeYJavaType ct, ImmutableList<KeYJavaType> signature) {
        List<? extends recoder.abstraction.Constructor> constructors = getRecoderConstructors(ct, signature);
        if (constructors.size() == 1) {
            return (IProgramMethod) rec2key().toKeY(constructors.get(0));
        }
        if (constructors.isEmpty()) {
            LOGGER.debug("javainfo: Constructor not found: {}", ct);
            return null;
        }
        Debug.fail();
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
            if (member instanceof IProgramMethod && ((IProgramMethod) member).getMethodDeclaration().getName().equals(name)) {
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
     * @param ct        the class type to get methods from.
     * @param m         the name of the methods in question.
     * @param signature the statical type signature of a callee.
     * @return the IProgramMethods, if one is found,
     * null if none or more than one IProgramMethod is found (in this case
     * a debug output is written to console).
     */
    public IProgramMethod getProgramMethod(KeYJavaType ct, String m, ImmutableList<? extends Type> signature, KeYJavaType context) {
        if (ct.getJavaType() instanceof ArrayType || context.getJavaType() instanceof ArrayType) {
            return getImplicitMethod(ct, m);
        }

        List<recoder.abstraction.Method> methodlist = getRecoderMethods(ct, m, signature, context);

        if (methodlist.size() == 1) {
            return (IProgramMethod) rec2key().toKeY(methodlist.get(0));
        } else if (methodlist.isEmpty()) {
            LOGGER.debug("javainfo: Program Method not found: {}", m);
            return null;
        } else {
            Debug.fail();
            return null;
        }
    }


    /**
     * returns the same fields as given in <tt>rfl</tt> and returns
     * their KeY representation
     *
     * @param rfl the List of fields to be looked up
     * @return list with the corresponding fields as KeY datastructures
     */
    private ImmutableList<Field> asKeYFields(List<? extends recoder.abstraction.Field> rfl) {
        ImmutableList<Field> result = ImmutableSLList.nil();
        if (rfl == null) {
            // this occurs for the artificial Null object at the moment
            // should it have implicit fields?
            return result;
        }
        for (int i = rfl.size() - 1; i >= 0; i--) {
            recoder.abstraction.Field rf = rfl.get(i);
            Field f = (Field) rec2key().toKeY(rf);
            if (f != null) {
                result = result.prepend(f);
            } else {
                LOGGER.debug("Field has no KeY equivalent (recoder field): {}", rf.getFullName());
                LOGGER.debug("This happens currently as classes only available in byte code " + "are only partially converted ");
            }
        }
        return result;
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
        recoder.abstraction.ClassType rct = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);

        return asKeYFields(rct.getProgramModelInfo().getFields(rct));
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

        recoder.abstraction.ClassType rct = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        List<recoder.abstraction.Field> rfl = rct.getProgramModelInfo().getAllFields(rct);

        return asKeYFields(rfl);
    }

    /**
     * returns all fields of and visible in an array field
     *
     * @param arrayType the KeYJavaType of the array
     * @return the list of visible fields
     */
    private ImmutableList<Field> getVisibleArrayFields(KeYJavaType arrayType) {
        ImmutableList<Field> result = ImmutableSLList.nil();

        final ImmutableArray<MemberDeclaration> members = ((ArrayDeclaration) arrayType.getJavaType()).getMembers();

        for (int i = members.size() - 1; i >= 0; i--) {
            final MemberDeclaration member = members.get(i);
            if (member instanceof FieldDeclaration) {
                final ImmutableArray<FieldSpecification> specs = ((FieldDeclaration) member).getFieldSpecifications();
                for (int j = specs.size() - 1; j >= 0; j--) {
                    result = result.prepend(specs.get(j));
                }
            }
        }

        //      fields of java.lang.Object visible in an array
        final ImmutableList<Field> javaLangObjectField = getAllVisibleFields((KeYJavaType) rec2key().toKeY(sc.getNameInfo().getJavaLangObject()));

        for (Field aJavaLangObjectField : javaLangObjectField) {
            if (!((recoder.abstraction.Field) rec2key().toRecoder(aJavaLangObjectField)).isPrivate()) {
                result = result.append(aJavaLangObjectField);
            }
        }
        return result;
    }

    /**
     * returns all proper subtypes of class <code>ct</code> (i.e. without <code>ct</code> itself)
     */
    private List<recoder.abstraction.ClassType> getAllRecoderSubtypes(KeYJavaType ct) {
        //TODO not possible
        //return sc.getCrossReferenceSourceInfo().getAllSubtypes((recoder.abstraction.ClassType) rec2key().toRecoder(ct));
    }

    /**
     * returns all supertypes of the given class type with the type itself as
     * first element
     *
     * @return
     */
    private List<ResolvedReferenceType> getAllRecoderSupertypes(KeYJavaType ct) {
        return getJPType(ct).resolve().asReferenceType().getAllAncestors();
    }


    /**
     * returns a list of KeYJavaTypes representing the given recoder types in
     * the same order
     *
     * @param rctl the ASTList<ClassType> to be converted
     * @return list of KeYJavaTypes representing the given recoder types in
     * the same order
     */
    private ImmutableList<KeYJavaType> asKeYJavaTypes(final List<recoder.abstraction.ClassType> rctl) {
        ImmutableList<KeYJavaType> result = ImmutableSLList.nil();
        for (int i = rctl.size() - 1; i >= 0; i--) {
            final recoder.abstraction.ClassType rct = rctl.get(i);
            final KeYJavaType kct = (KeYJavaType) rec2key().toKeY(rct);
            if (kct != null) {
                result = result.prepend(kct);
            }
        }
        return result;
    }

    /**
     * Returns all known supertypes of the given class type with the type itself
     * as first element.
     *
     * @param ct a class type
     * @return the list of the known subtypes of the given class type.
     */
    public ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType ct) {
        return asKeYJavaTypes(getAllRecoderSupertypes(ct));
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

    private JP2KeYConverter createRecoder2KeY(NamespaceSet nss) {
        return new Recoder2KeY(services, rec2key(), nss, typeConverter);
    }

    /**
     * Parses a given JavaBlock using cd as context to determine the right
     * references.
     *
     * @param block a String describing a java block
     * @param cd    ClassDeclaration representing the context in which the
     *              block has to be interpreted.
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, ClassDeclaration cd, NamespaceSet nss) {
        return createRecoder2KeY(nss).readBlock(block,
                new JPContext(sc, (recoder.java.declaration.ClassDeclaration) rec2key().toRecoder(cd)));
    }


    /**
     * Parses a given JavaBlock using an empty context.
     *
     * @param block a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readJavaBlock(String block, NamespaceSet nss) {
        return createRecoder2KeY(nss).readBlockWithEmptyContext(block);
    }


    public ImmutableList<KeYJavaType> findImplementations(Type ct, String name, ImmutableList<KeYJavaType> signature) {

        // set up recoder inputs
        recoder.abstraction.ClassType rct = (recoder.abstraction.ClassType) rec2key().toRecoder(ct);
        // transform the signature up to recoder conventions
        ArrayList<recoder.abstraction.Type> rsignature = new ArrayList<>(signature.size());
        Iterator<KeYJavaType> i = signature.iterator();
        int j = 0;
        while (i.hasNext()) {
            rsignature.add(j, (recoder.abstraction.Type) rec2key().toRecoder(i.next()));
            j++;
        }

        // If ct is an interface, but does not declare the method, we
        // need to start the search "upstairs"

        while (rct.isInterface() && !isDeclaringInterface(rct, name, rsignature)) {
            rct = rct.getAllSupertypes().get(1);
        }


        ImmutableList<KeYJavaType> classList = ImmutableSLList.nil();
        classList = recFindImplementations(rct, name, rsignature, classList);


        if (!declaresApplicableMethods(rct, name, rsignature)) {
            // ct has no implementation, go up
            List<recoder.abstraction.ClassType> superTypes = rct.getAllSupertypes();
            int k = 0;
            while (k < superTypes.size() && !declaresApplicableMethods(superTypes.get(k), name, rsignature)) k++;
            if (k < superTypes.size()) {
                rct = superTypes.get(k);
                KeYJavaType r = (KeYJavaType) mapping.toKeY(rct);
                if (r == null) {
                    LOGGER.info("Type {}", rct.getName());
                } else {
                    classList = classList.append(r);
                }
            } // no implementation is needed if classes above are abstract
        }

        return classList;
    }


    private ImmutableList<KeYJavaType> recFindImplementations(recoder.abstraction.ClassType ct, String name, List<recoder.abstraction.Type> signature, ImmutableList<KeYJavaType> result) {
        recoder.service.CrossReferenceSourceInfo si = getServConf().getCrossReferenceSourceInfo();

        if (declaresApplicableMethods(ct, name, signature)) {
            KeYJavaType r = (KeYJavaType) mapping.toKeY(ct);
            if (r == null) {
                LOGGER.info("Type {}: {} not found", ct.getFullName(), name);
            } else if (!result.contains(r)) {
                result = result.prepend(r);
            }
        }

        List<recoder.abstraction.ClassType> classes = si.getSubtypes(ct);

        //alpha sorting to make order deterministic
        recoder.abstraction.ClassType[] classesArray = classes.toArray(new ClassType[0]);
        java.util.Arrays.sort(classesArray, (o1, o2) -> o2.getFullName().compareTo(o1.getFullName()));

        for (recoder.abstraction.ClassType c : classesArray) {
            result = recFindImplementations(c, name, signature, result);
        }
        return result;
    }


    private boolean declaresApplicableMethods(recoder.abstraction.ClassType ct, String name, List<recoder.abstraction.Type> signature) {
        recoder.service.CrossReferenceSourceInfo si = getServConf().getCrossReferenceSourceInfo();

        List<recoder.abstraction.Method> list = si.getMethods(ct);
        int s = list.size();
        int i = 0;
        while (i < s) {
            recoder.abstraction.Method m = list.get(i);
            if (name.equals(m.getName()) && si.isCompatibleSignature(signature, m.getSignature()) && si.isVisibleFor(m, ct) && !m.isAbstract())
                return true;
            else i++;
        }
        return false;
    }

    private boolean isDeclaringInterface(recoder.abstraction.ClassType ct, String name, List<recoder.abstraction.Type> signature) {
        Debug.assertTrue(ct.isInterface());
        List<recoder.abstraction.Method> list = si.getMethods(ct);
        int s = list.size();
        int i = 0;
        while (i < s) {
            recoder.abstraction.Method m = list.get(i);
            if (name.equals(m.getName()) && si.isCompatibleSignature(signature, m.getSignature()) && si.isVisibleFor(m, ct))
                return true;
            else i++;
        }
        return false;
    }

    private void putImplicitMethod(IProgramMethod m, KeYJavaType t) {
        Map<String, IProgramMethod> map = implicits.computeIfAbsent(t, k -> new LinkedHashMap<>());
        map.put(m.name().toString(), m);
    }


    public JPKeYProgModelInfo copy() {
        return new JPKeYProgModelInfo(services, rec2key().copy(), typeConverter, exceptionHandler);
    }
}