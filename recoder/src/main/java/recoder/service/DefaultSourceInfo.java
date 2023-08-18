/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.IllegalTransformationException;
import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.*;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.kit.MiscKit;
import recoder.kit.StatementKit;
import recoder.kit.UnitKit;
import recoder.list.generic.ASTList;
import recoder.service.DefaultNameInfo.UnknownClassType;
import recoder.util.Debug;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

/**
 * Implements queries for program model elements with concrete syntactical representations.
 *
 * @author RN, AL, DH, VK, TG
 */
public class DefaultSourceInfo extends DefaultProgramModelInfo
        implements SourceInfo, ChangeHistoryListener, Formats {

    private final static boolean DEBUG = false;
    private final static int CONSTANT_FALSE = 0;
    private final static int CONSTANT_TRUE = 1;
    private final static int NOT_CONSTANT = -1;
    /**
     * Performance cache for predefined primitive types and array types. protected for KeY
     */
    protected final Map<String, Type> name2primitiveType =
        new HashMap<>(INITIAL_SOURCE_INFO_NAME2PRIMITIVE_HASH_SET_SIZE);
    /**
     * Cache mapping (package|type|variable|method|constructor)references to program model elements:
     * <Reference, ProgramModelElement>
     */
    final Map<Reference, ProgramModelElement> reference2element =
        new HashMap<>(
            INITIAL_SOURCE_INFO_REFERENCE2ELEMENT_HASH_SET_SIZE);
    final ProgressListenerManager listeners = new ProgressListenerManager(this);

    /**
     * Creates a new service.
     *
     * @param config the configuration this services becomes part of.
     */
    public DefaultSourceInfo(ServiceConfiguration config) {
        super(config);
    }

    /**
     * determines whether or not the given element is part of a tree node of the given type.
     * Especially, this is true if the program element is itself an object of the given class.
     *
     * @param pe the program element to be checked
     * @param c the class type of the expected parent
     * @return true iff any tree parent (including pe itself) is an instance of c
     */
    static boolean isPartOf(ProgramElement pe, Class c) {
        while (pe != null && !c.isInstance(pe)) {
            pe = pe.getASTParent();
        }
        return pe != null;
    }

    /**
     * looks for the next variable scope that is a parent of the given element
     *
     * @param pe a program element
     * @return the outer variable scope of the program element or <tt>null</tt>
     */
    private static VariableScope findOuterVariableScope(VariableScope ts) {
        NonTerminalProgramElement pe = ts.getASTParent();
        while (pe != null && !(pe instanceof VariableScope)) {
            pe = pe.getASTParent();
        }
        return (VariableScope) pe;
    }

    private static void addSequentialFollower(Statement s, List<Statement> list) {
        Debug.assertNonnull(s);
        StatementContainer parent = s.getStatementContainer();
        while (true) {
            int c = parent.getStatementCount();
            int p = 0;
            while (parent.getStatementAt(p) != s) {
                p += 1;
            }
            if (p < c - 1) {
                list.add(parent.getStatementAt(p + 1));
                break;
            }
            if (parent instanceof MemberDeclaration) {
                list.add(METHOD_EXIT);
                break;
            }
            if (parent instanceof Statement) {
                if (parent instanceof LoopStatement) {
                    LoopStatement loop = (LoopStatement) parent;

                    list.add(loop);
                    return;
                }
                s = (Statement) parent;
                parent = ((Statement) parent).getStatementContainer();
            } else {
                while (parent instanceof Branch) {
                    s = ((Branch) parent).getParent();
                    parent = s.getStatementContainer();
                }
            }
        }
    }

    // LoopStatement or Switch
    private static Statement findInnermostBreakBlock(Statement s) {
        NonTerminalProgramElement parent = s.getStatementContainer();
        while (parent != null && !(parent instanceof MemberDeclaration)) {
            if ((parent instanceof LoopStatement) || (parent instanceof Switch)) {
                return (Statement) parent;
            }
            parent = parent.getASTParent();
        }
        return null;
    }

    private static LoopStatement findInnermostLoop(Statement s) {
        NonTerminalProgramElement parent = s.getStatementContainer();
        while (parent != null && !(parent instanceof MemberDeclaration)) {
            if (parent instanceof LoopStatement) {
                return (LoopStatement) parent;
            }
            parent = parent.getASTParent();
        }
        return null;
    }

    /**
     * Initializes the new service; called by the configuration.
     *
     * @param config the configuration this services becomes part of.
     */
    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        cfg.getChangeHistory().addChangeHistoryListener(this);
        NameInfo ni = getNameInfo();
        name2primitiveType.put("boolean", ni.getBooleanType());
        name2primitiveType.put("char", ni.getCharType());
        name2primitiveType.put("int", ni.getIntType());
        name2primitiveType.put("float", ni.getFloatType());
        name2primitiveType.put("double", ni.getDoubleType());
        name2primitiveType.put("byte", ni.getByteType());
        name2primitiveType.put("short", ni.getShortType());
        name2primitiveType.put("long", ni.getLongType());
        name2primitiveType.put("boolean[]", ni.createArrayType(ni.getBooleanType()));
        name2primitiveType.put("char[]", ni.createArrayType(ni.getCharType()));
        name2primitiveType.put("int[]", ni.createArrayType(ni.getIntType()));
        name2primitiveType.put("float[]", ni.createArrayType(ni.getFloatType()));
        name2primitiveType.put("double[]", ni.createArrayType(ni.getDoubleType()));
        name2primitiveType.put("byte[]", ni.createArrayType(ni.getByteType()));
        name2primitiveType.put("short[]", ni.createArrayType(ni.getShortType()));
        name2primitiveType.put("long[]", ni.createArrayType(ni.getLongType()));
    }

    public void addProgressListener(ProgressListener l) {
        listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        listeners.removeProgressListener(l);
    }

    protected NameInfo getNameInfo() {
        return super.getNameInfo();
    }

    /**
     * Change notification callback method.
     *
     * @param config the configuration this services becomes part of.
     */
    public void modelChanged(ChangeHistoryEvent changes) {
        List<TreeChange> changed = changes.getChanges();
        int s = changed.size();

        listeners.fireProgressEvent(0, s);
        int c = 0;

        // detached first
        for (TreeChange tc : changed) {
            if (!tc.isMinor() && (tc instanceof DetachChange)) {
                processChange(tc);
                listeners.fireProgressEvent(++c);
            }
        }
        for (TreeChange tc : changed) {
            if (!tc.isMinor() && (tc instanceof AttachChange)) {
                processChange(tc);
                listeners.fireProgressEvent(++c);
            }
        }
    }

    /**
     * handles the given change by trying not to invalidate too much pre computed information.
     *
     * @param attached true if the program elements was attached, false otherwise
     * @param changed the program element that was changed
     */
    void processChange(TreeChange change) {
        // the following code implements a very restrictive way to invalidate
        // previously computed information.
        ProgramElement changed = change.getChangeRoot();
        if (isPartOf(changed, PackageSpecification.class) || isPartOf(changed, Import.class)
                || determinesGlobalEntityName(changed) || determinesGlobalEntityType(changed)) {
            // pessimistically clear the caches
            super.reset();
            reference2element.clear();
            /*
             * The class type cache could be reused for most part. However, since the cross
             * referencer resets the caches, extra handling is not really worthwhile here.
             */
        }
        // if package specification, update NameInfo (which can reuse old cache entries)
        if (changed instanceof PackageSpecification) {
            PackageSpecification pkgSpec = (PackageSpecification) changed;
            boolean isAttach = change instanceof AttachChange;
            handleCUPackageChange(pkgSpec.getParent(),
                Naming.toPathName(pkgSpec.getPackageReference()), isAttach);
        }
        if (changed instanceof PackageReference && isPartOf(changed, PackageSpecification.class)) {
            // TODO !!!
            // TODO see also DefaultNameInfo.getType(String) - prints warning as well
            System.err.println(
                "WARNING: name info may now contain invalid mappings name2type... (TO BE FIXED)");
        }
        if (changed instanceof Identifier) {
            NonTerminalProgramElement par = changed.getASTParent();
            if (change instanceof AttachChange) {
                register(par);
            } else {
                String oldname = ((Identifier) changed).getText();
                if (par instanceof VariableSpecification) {
                    unregister((VariableSpecification) par, oldname);
                } else if (par instanceof TypeDeclaration) {
                    unregister((TypeDeclaration) par, oldname);
                }
            }
            // now inform NameInfo
            processIdentifierChanged(change);
        } else {
            if (change instanceof AttachChange) {
                register(changed);
            } else {
                unregister(changed);
            }
        }
    }

    private void handleCUPackageChange(CompilationUnit cu, String originalPkgName,
            boolean isAttach) {
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        for (int j = 0, l = cu.getTypeDeclarationCount(); j < l; j++) {
            ClassType ct = cu.getTypeDeclarationAt(j);
            String fullPath =
                originalPkgName + ("".equals(originalPkgName) ? "" : ".") + ct.getName();
            String defaultPkgPath = ct.getName();
            if (isAttach) {
                dni.handleTypeRename(ct, defaultPkgPath, fullPath);
            } else {
                dni.handleTypeRename(ct, fullPath, defaultPkgPath);
            }
        }
    }

    private void processIdentifierChanged(TreeChange tc) {
        if (!(getNameInfo() instanceof DefaultNameInfo)) {
            return;
        }

        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        Identifier id = (Identifier) tc.getChangeRoot();
        NonTerminalProgramElement npe = id.getParent();
        /*
         * an identifier could be used by: - LabeledStatement (ignore) - MethodDeclaration (ignore)
         * - TypeDeclaration (handle) - VariableSpecification (ignore) - FieldSpecification (handle)
         * - any subtype of NameReference (ignore) - package reference -> parent is package
         * specification (handle)
         */
        if (npe instanceof TypeDeclaration) {
            TypeDeclaration td = (TypeDeclaration) npe;
            // name info will automatically conserve array references (see there)
            if (tc instanceof AttachChange) {
                Object old = dni.getType(td.getFullName());
                if (old == null || old == dni.getUnknownType()) {
                    dni.register(td); // otherwise, we got a nameclash; preserve first
                }
            } else {
                Object old = dni.getType(td.getFullName());
                if (old == td) // special handling which might occur if a nameclash happened before,
                               // which would now be resolved
                {
                    dni.unregisterClassType(td.getFullName(), true);
                }
            }
        } else if (npe instanceof FieldSpecification) {
            FieldSpecification fs = (FieldSpecification) npe;
            if (tc instanceof AttachChange) {
                dni.register(fs);
            } else {
                dni.unregisterField(fs.getFullName());
            }
        } else if (npe instanceof PackageReference && isPartOf(npe, PackageSpecification.class)) {
            // while (!(npe instanceof PackageSpecification)) npe = npe.getASTParent();
            // PackageSpecification ps = (PackageSpecification)npe;
            // Package p = (Package)oldReference2Element.get(ps.getPackageReference());
            // if (p == null)
            // p = (Package)reference2element.get(ps.getPackageReference());
            // String oldpname = p.getFullName();
            // boolean isAttach = (tc instanceof AttachChange);
            // handleCUPackageChange(ps.getParent(), oldpname, isAttach);
            throw new IllegalTransformationException(
                "Changing an Identifier contained in a PackageSpecification is not valid."
                    + " Change either the containing PackageReference or PackageSpecification instead.");
        }
    }

    /**
     * determines whether or not the given progran element is the name of a "globally" visible
     * entity.
     *
     * @param pe the program element to be checked
     * @return true iff the given element deteremines the name or is part of the name of an entity.
     */
    private boolean determinesGlobalEntityName(ProgramElement pe) {
        if (pe instanceof Identifier) {
            ProgramElement parent = pe.getASTParent();
            return (parent instanceof MemberDeclaration);
        }
        return false;
    }

    /**
     * determines whether or not the given progran element specifies the type of a "globally"
     * visible entity.
     *
     * @param pe the program element to be checked
     * @return true iff the given element deteremines the type or is part of the type specification.
     */
    private boolean determinesGlobalEntityType(ProgramElement pe) {
        return isPartOf(pe, TypeReference.class) && (isPartOf(pe, FieldDeclaration.class)
                || isPartOf(pe, InheritanceSpecification.class));
    }

    private ProgramElement getDeclaration(ProgramModelElement pme) {
        return (pme instanceof ProgramElement) ? (ProgramElement) pme : null;
    }

    public final TypeDeclaration getTypeDeclaration(ClassType ct) {
        return (ct instanceof TypeDeclaration) ? (TypeDeclaration) ct : null;
    }

    public final MethodDeclaration getMethodDeclaration(Method m) {
        return (m instanceof MethodDeclaration) ? (MethodDeclaration) m : null;
    }

    public final VariableSpecification getVariableSpecification(Variable v) {
        return (v instanceof VariableSpecification) ? (VariableSpecification) v : null;
    }

    public final ConstructorDeclaration getConstructorDeclaration(Constructor c) {
        return (c instanceof ConstructorDeclaration) ? (ConstructorDeclaration) c : null;
    }

    /* protected for KeY */
    protected ClassType getFromUnitPackage(String name, CompilationUnit cu) {
        String xname = Naming.getPackageName(cu);
        if (xname.length() > 0) {
            xname = Naming.dot(xname, name);
        }
        if (DEBUG) {
            Debug.log("Checking unit package type " + xname);
        }
        return getNameInfo().getClassType(xname);
    }

    // traverse *all* directly imported types
    /* protected for KeY */
    protected ClassType getFromTypeImports(String name, List<Import> il) {
        if (DEBUG) {
            Debug.log("Checking " + name + " in type imports");
        }
        ClassType result = null;
        NameInfo ni = getNameInfo();
        for (int i = il.size() - 1; i >= 0; i -= 1) {
            Import imp = il.get(i);
            if (imp.isMultiImport()) {
                continue;
            }
            TypeReference tr = imp.getTypeReference();
            ClassType newResult = null;
            String trname =
                imp.isStaticImport() ? imp.getStaticIdentifier().getText() : tr.getName();
            if (DEBUG) {
                Debug.log(" Checking against " + trname);
            }
            // trname must end with the start of name
            if (name.startsWith(trname)) {
                int tlen = trname.length();
                int nlen = name.length();
                // the start of name must be a prefix (ending with '.')
                if (tlen == nlen || name.charAt(tlen) == '.') {
                    // if static, tr is referenceprefix of the static identifier
                    ReferencePrefix rp = imp.isStaticImport() ? tr : tr.getReferencePrefix();
                    if (rp == null) {
                        // direct import of requested type
                        trname = name;
                    } else {
                        // import of a valid prefix of the requested type
                        trname = Naming.toPathName(rp, name);
                    }
                    newResult = ni.getClassType(trname);
                    if (DEBUG) {
                        Debug.log(" Trying " + trname);
                        Debug.log(Format.toString(" Found %N", newResult));
                    }
                }
            } else if (name.endsWith(trname) && name.equals(trname = Naming.toPathName(tr))) {
                newResult = ni.getClassType(trname);
            }
            // newResult may be invalid if type is not static, but this is a static import
            if (newResult != null && (newResult.isStatic() || !imp.isStaticImport())) {
                if (result != null && result != newResult) {
                    getErrorHandler()
                            .reportError(
                                new AmbiguousImportException(
                                    "Ambiguous import " + Format.toString(ELEMENT_LONG, imp)
                                        + " - could be " + Format.toString("%N", result) + " or "
                                        + Format.toString("%N", newResult),
                                    imp, result, newResult));
                    // ignore if forced to do so
                }
                result = newResult;
            }
        }
        return result;
    }

    protected ErrorHandler getErrorHandler() {
        return super.getErrorHandler();
    }

    // traverse *all* imported packages (to check for ambiguities)
    /* protected for KeY */
    protected ClassType getFromPackageImports(String name, List<Import> il,
            ClassType searchingFrom) {
        if (DEBUG) {
            Debug.log("Checking " + name + " in package imports");
        }
        ClassType result = null;
        NameInfo ni = getNameInfo();
        for (int i = il.size() - 1; i >= 0; i--) {
            Import imp = il.get(i);
            if (imp.isMultiImport()) {
                TypeReferenceInfix ref = imp.getReference();
                String xname = Naming.toPathName(ref, name);
                if (DEBUG) {
                    Debug.log("Checking wildcard type " + xname);
                }
                ClassType newResult = ni.getClassType(xname);
                // pretend not to have seen package-visible types
                if ((!imp.isStaticImport() && newResult != null && !newResult.isPublic())
                        || (imp.isStaticImport() && newResult != null
                                && !isVisibleFor(newResult, searchingFrom))) {
                    newResult = null;
                }
                // newResult may be invalid if it's non-static but import is static
                if (newResult != null && (newResult.isStatic() || !imp.isStaticImport())) {
                    if (result != null && result != newResult) {
                        getErrorHandler()
                                .reportError(new AmbiguousImportException(
                                    "Ambiguous import of type " + name + ": could be "
                                        + Format.toString("%N", result) + " or "
                                        + Format.toString("%N", newResult),
                                    imp, result, newResult));
                        // ignore problem to resume
                    }
                    result = newResult;
                }
            }
        }
        return result;
    }

    /**
     * Searches the given short name as a member type of the given class.
     */
    private ClassType getMemberType(String shortName, ClassType ct) {
        if (DEBUG) {
            Debug.log("Checking for type " + shortName + " within " + ct.getFullName());
        }
        List<? extends ClassType> innerTypes = ct.getTypes();
        for (int i = innerTypes.size() - 1; i >= 0; i -= 1) {
            ClassType candid = innerTypes.get(i);
            if (shortName.equals(candid.getName())) {
                return candid;
            }
        }
        // search supertypes
        List<? extends ClassType> superTypes = ct.getSupertypes();
        for (ClassType possibleSuperclass : superTypes) {
            // fixed in recoder 0.80: interfaces may contain member interfaces
            ClassType result = getMemberType(shortName, possibleSuperclass);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * Searches the given type name in the given scope. The name may be a partial name such as
     * <CODE>A.B</CODE> where <CODE>b</CODE> is a member class of <CODE>A</CODE>.
     */
    protected ClassType getLocalType(String name, TypeScope scope) {
        ClassType result = null;
        int dotPos = name.indexOf('.');
        String shortName = (dotPos == -1) ? name : name.substring(0, dotPos);
        if (DEBUG) {
            String output = "Looking for type " + shortName + " in scope of "
                + Format.toString("%c[%p]: ", scope);
            List<? extends ClassType> ctl = scope.getTypesInScope();
            if (ctl != null && ctl.size() > 0) {
                output += " " + Format.toString("%n", ctl);
            }
            Debug.log(output);
        }
        result = scope.getTypeInScope(shortName);
        while (result != null && dotPos != -1) {
            dotPos += 1;
            int nextDotPos = name.indexOf('.', dotPos);
            shortName =
                (nextDotPos == -1) ? name.substring(dotPos) : name.substring(dotPos, nextDotPos);
            dotPos = nextDotPos;
            result = getMemberType(shortName, result);
        }
        return result;
    }

    /**
     * Searches an inherited member type of the given name. The method does also report locally
     * defined member types of the given type.
     */
    protected ClassType getInheritedType(String name, ClassType ct) {
        int dotPos = name.indexOf('.');
        String shortName = (dotPos == -1) ? name : name.substring(0, dotPos);
        // it does not pay to check if ct has any non-trivial supertypes
        List<ClassType> ctl = getAllTypes(ct);
        if (DEBUG) {
            Debug.log("Checking type " + shortName + " as inherited member of " + ct.getFullName()
                + ": " + Format.toString("%N", ctl));
        }
        ClassType result = null;
        int nc = ctl.size();
        // starting at i = ct.getTypes().size() would have little to no
        // influence on performance
        for (ClassType c : ctl) {
            if (shortName.equals(c.getName())) {
                result = c;
                break;
            }
        }
        while (result != null && dotPos != -1) {
            dotPos += 1;
            int nextDotPos = name.indexOf('.', dotPos);
            shortName =
                (nextDotPos == -1) ? name.substring(dotPos) : name.substring(dotPos, nextDotPos);
            dotPos = nextDotPos;
            result = getMemberType(shortName, result);
        }
        return result;
    }

    /**
     * Tries to find a type with the given name using the given program element as context. Useful
     * to check for name clashes when introducing a new identifier. Neither name nor context may be
     * <CODE>null</CODE>.
     *
     * @param name the name for the type to be looked up; may or may not be qualified.
     * @param context a program element defining the lookup context (scope).
     * @return the corresponding type (may be <CODE>null</CODE>).
     */
    public Type getType(String name, ProgramElement context) {
        Debug.assertNonnull(name, context);

        NameInfo ni = getNameInfo();

        // check primitive types, array types of primitive types,
        // and void --- these happen often
        Type t = name2primitiveType.get(name);
        if (t != null) {
            return t;
        }
        if (name.equals("void")) {
            return null;
        }
        // catch array types
        if (name.endsWith("]")) {
            int px = name.indexOf('[');
            // compute base type
            Type baseType = getType(name.substring(0, px), context);
            if (baseType == null) {
                return null;
            }
            String indexExprs = name.substring(px);
            // the basetype exists now, so fetch a corresponding array type
            // (if there is none, the name info will create one)
            return ni.getType(baseType.getFullName() + indexExprs);
        }

        if (DEBUG) {
            Debug.log("Looking for type " + name + Format.toString(" @%p in %u", context));
        }

        updateModel();

        // in the very special case that we are asking from the point of
        // view of a supertype reference, we must move to the enclosing unit
        // or parent type
        if (context.getASTParent() instanceof InheritanceSpecification) {
            context = context.getASTParent().getASTParent().getASTParent();
        }

        ProgramElement pe = context;
        while (pe != null && !(pe instanceof TypeScope)) {
            context = pe;
            pe = pe.getASTParent();
        }
        TypeScope scope = (TypeScope) pe;
        if (scope == null) {
            Debug.log("Null scope during type query " + name + " in context "
                + Format.toString(Formats.ELEMENT_LONG, context));
            Debug.log(Debug.makeStackTrace());
        }
        ClassType result = null;

        // do the scope walk
        TypeScope s = scope;
        while (s != null) {
            result = getLocalType(name, s);
            if (result != null) {
                // must double check this result - rare cases of confusion
                // involving type references before a local class of the
                // corresponding name has been specified
                if (s instanceof StatementBlock) {
                    StatementContainer cont = (StatementBlock) s;
                    for (int i = 0; true; i += 1) {
                        Statement stmt = cont.getStatementAt(i);
                        if (stmt == result) {
                            // stop if definition comes first
                            break;
                        }
                        if (stmt == context) {
                            // tricky: reference before definition - must
                            // ignore the definition :(
                            result = null;
                            break;
                        }
                    }
                }
                if (result != null) {
                    // leave _now_
                    break;
                }
            }
            if (s instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) s;
                ClassType newResult = getInheritedType(name, td);

                if (newResult != null) {
                    if (result == null) {
                        if (DEBUG) {
                            Debug.log("Found type " + name + " inherited in type scope "
                                + td.getFullName());
                        }
                        result = newResult;
                        break;
                    } else if (result != newResult) {
                        // !!!!!!! Problematic if this is a speculative
                        // question - do we really want to bail out?
                        getErrorHandler().reportError(new AmbiguousReferenceException("Type "
                            + Format.toString("%N", newResult)
                            + " is an inherited member type that is also defined as outer member type "
                            + Format.toString("%N", result), null, result, newResult));
                        break;
                    }
                }
            }
            scope = s;
            pe = s.getASTParent();
            while (pe != null && !(pe instanceof TypeScope)) {
                context = pe;
                pe = pe.getASTParent();
            }
            s = (TypeScope) pe;
        }
        if (result != null) {
            if (DEBUG) {
                Debug.log(Format.toString("Found %N", result));
            }
            return result;
        }

        // now the outer scope is null, so we have arrived at the top
        CompilationUnit cu = (CompilationUnit) scope;

        List<Import> il = cu.getImports();
        if (il != null) {
            // first check type imports
            result = getFromTypeImports(name, il);
        }
        if (result == null) {
            // then check same package
            result = getFromUnitPackage(name, cu);
            if (result == null && il != null) {
                // then check package imports
                result = getFromPackageImports(name, il,
                    cu.getTypeDeclarationAt(0 /*
                                               * doesn't matter which one to check, since this is
                                               * important for static imports only
                                               */));
            }
        }
        if (result == null) {
            // check global types: if unqualified, attempt "java.lang.<name>":
            // any unqualified local type would have been imported already!
            String defaultName = Naming.dot("java.lang", name);
            if (DEBUG) {
                Debug.log("Checking type " + defaultName);
            }
            result = ni.getClassType(defaultName);
            if (result == null) {
                if (DEBUG) {
                    Debug.log("Checking type " + name);
                }
                result = ni.getClassType(name);
            }
        }
        if (result != null) {
            scope.addTypeToScope(result, name); // add it to the CU scope
        }
        if (DEBUG) {
            Debug.log(Format.toString("Found %N", result));
        }
        return result;
    }

    public Type getType(TypeReference tr) {
        Type res = (Type) reference2element.get(tr);
        if (res != null) {
            return res;
        }
        ReferencePrefix rp = tr.getReferencePrefix();
        if (rp instanceof PackageReference) {
            String name = Naming.toPathName(rp, tr.getName());
            res = getNameInfo().getClassType(name);
            if (res != null) {
                for (int d = tr.getDimensions(); d > 0; d -= 1) {
                    res = getNameInfo().createArrayType(res);
                }
            }
        } else {
            res = getType(Naming.toPathName(tr), tr);
        }
        if (res == null && !"void".equals(tr.getName())) {
            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + "(14)", tr), tr));
            res = getNameInfo().getUnknownType();
        }
        if (res != null) {
            if (tr.getTypeArguments() != null && tr.getTypeArguments().size() != 0) {
                if (res instanceof ArrayType) {
                    // this happens if variable is declared like this:
                    // MyClass<String>[] m;
                    // but not if like this:
                    // MyClass<String> m[];
                    res = makeParameterizedArrayType(res, tr.getTypeArguments());
                } else {
                    res = new ParameterizedType((ClassType) res, tr.getTypeArguments());
                }
            }
            reference2element.put(tr, res);
        }
        return res;
    }

    public final ClassType getType(TypeDeclaration td) {
        return td;
    }

    public Type getType(VariableSpecification vs) {
        if (vs instanceof EnumConstantSpecification) {
            return getType((EnumConstantSpecification) vs);
        }
        updateModel(); // probably not necessary
        TypeReference tr = (vs.getParent()).getTypeReference();
        Type result = getType(tr);
        if (result != null) {
            int d = vs.getDimensions();
            if (vs.getASTParent() instanceof ParameterDeclaration) {
                ParameterDeclaration pd = (ParameterDeclaration) vs.getASTParent();
                if (pd.isVarArg()) {
                    d++;
                }
            }
            for (; d > 0; d -= 1) {
                result = getNameInfo().createArrayType(result);
            }
        }
        return result;
    }

    private Type getType(EnumConstantSpecification ecs) {
        Type cd = ecs.getConstructorReference().getClassDeclaration();
        if (cd != null) {
            return cd; // anonymous type
        }
        return ecs.getParent().getParent(); // enum type itself
    }

    /**
     * Returns the type of the given program element. For declarations, this is the type declared by
     * the given declaration, for references, this means the referenced type, and for expressions
     * this is the result type.
     * <p>
     * WARNING: Most of the times, DefaultNameInfo.getUnknownType() is returned instead of
     * <code>null</code> iff type is unknown. This is the desired behaviour, however, it's not
     * implemented 100% consistently (TODO!!)
     *
     * @param pe the program element to analyze.
     * @return the type of the program element or <tt>null</tt> if the type is void;
     *         <tt>DefaultNameInfo.unknownClassType</tt> if the type is unknown or unavailable.
     */
    public Type getType(ProgramElement pe) {
        updateModel();
        Type result = null;
        if (pe instanceof Expression) {
            result = getType((Expression) pe);
        } else if (pe instanceof UncollatedReferenceQualifier) {
            result = getType((UncollatedReferenceQualifier) pe);
        } else if (pe instanceof TypeReference) {
            result = getType((TypeReference) pe);
        } else if (pe instanceof VariableSpecification) {
            result = getType((VariableSpecification) pe);
        } else if (pe instanceof EnumConstantSpecification) {
            result = getType((EnumConstantSpecification) pe);
        } else if (pe instanceof MethodDeclaration) {
            if (!(pe instanceof ConstructorDeclaration)) {
                result = getReturnType((MethodDeclaration) pe);
            }
        } else if (pe instanceof TypeDeclaration) {
            result = getType((TypeDeclaration) pe);
        }
        return result;
    }

    private Type getType(UncollatedReferenceQualifier urq) {
        Reference r = resolveURQ(urq);
        if (r instanceof UncollatedReferenceQualifier) {
            // resolution failed, continue anyway
            return getNameInfo().getUnknownClassType();
        }
        return getType(r);
    }

    public Type getType(Expression expr) {
        Type result = null;
        if (expr instanceof Operator) { ///////////////// Operators
            Operator op = (Operator) expr;
            ASTList<Expression> args = op.getArguments();
            if (op instanceof Assignment) {
                result = getType(args.get(0));
            } else if ((op instanceof TypeCast) || (op instanceof New)) {
                result = getType(((TypeOperator) op).getTypeReference());
            } else if (op instanceof NewArray) {
                NewArray n = (NewArray) op;
                TypeReference tr = n.getTypeReference();
                result = getType(tr);
                for (int d = n.getDimensions(); d > 0; d -= 1) {
                    Type oldResult = result;
                    result = getNameInfo().getArrayType(result);
                    if (result == null) {
                        result = getNameInfo().createArrayType(oldResult);
                    }
                }
            } else if ((op instanceof PreIncrement) || (op instanceof PostIncrement)
                    || (op instanceof PreDecrement) || (op instanceof PostDecrement)
                    || (op instanceof ParenthesizedExpression) || (op instanceof BinaryNot)) {
                result = getType(args.get(0));
            } else if ((op instanceof Positive) || (op instanceof Negative)) {
                result = getType(args.get(0));
                if (java5Allowed() && result instanceof ClassType) {
                    result = getUnboxedType((ClassType) result);
                }
            } else if ((op instanceof Plus) || (op instanceof Minus) || (op instanceof Times)
                    || (op instanceof Divide) || (op instanceof Modulo)) {
                Type t1 = getType(args.get(0));
                Type t2 = getType(args.get(1));

                if (java5Allowed()) {
                    if ((t1 instanceof PrimitiveType) ^ (t2 instanceof PrimitiveType)) {
                        if (t1 instanceof ClassType) {
                            t1 = getUnboxedType((ClassType) t1);
                        } else if (t2 instanceof ClassType) {
                            t2 = getUnboxedType((ClassType) t2);
                        }
                    }
                }

                if ((op instanceof Plus) && ((t1 == getNameInfo().getJavaLangString())
                        || (t2 == getNameInfo().getJavaLangString()) || (t1 == null)
                        || (t2 == null))) {
                    // all primitive types are known -
                    // one of these must be a class type
                    result = getNameInfo().getJavaLangString();
                    // any object-plus-operation must result in a string type
                } else if ((t1 instanceof PrimitiveType) && (t2 instanceof PrimitiveType)) {
                    result = getPromotedType((PrimitiveType) t1, (PrimitiveType) t2);
                    if (result == null) {
                        getErrorHandler().reportError(
                            new TypingException("Boolean types cannot be promoted in " + op, op));
                        result = getNameInfo().getUnknownType();
                    }
                } else {
                    if ((t1 != null) && (t2 != null)) {
                        getErrorHandler()
                                .reportError(new TypingException("Illegal operand types for plus "
                                    + t1 + " + " + t2 + " in expression " + op, op));
                        result = getNameInfo().getUnknownType();
                    }
                }
            } else if ((op instanceof ShiftRight) || (op instanceof UnsignedShiftRight)
                    || (op instanceof ShiftLeft) || (op instanceof BinaryAnd)
                    || (op instanceof BinaryOr) || (op instanceof BinaryXOr)) {
                Type t1 = getType(args.get(0));
                if (java5Allowed()) {
                    Type t2 = getType(args.get(1));
                    if (t1 instanceof ClassType && t2 instanceof PrimitiveType) {
                        t1 = getUnboxedType((ClassType) t1);
                    }
                }
                result = t1;
            } else if ((op instanceof ComparativeOperator) || (op instanceof LogicalAnd)
                    || (op instanceof LogicalOr) || (op instanceof LogicalNot)
                    || (op instanceof Instanceof)) {
                result = getNameInfo().getBooleanType();
            } else if (op instanceof Conditional) {
                Expression e1 = args.get(1);
                Expression e2 = args.get(2);
                Type t1 = getType(e1);
                Type t2 = getType(e2);
                if (java5Allowed()) {
                    // (un-)boxing support (see JLS 3rd edition pg. 511)
                    if (t1 instanceof PrimitiveType && t2 instanceof ClassType) {
                        Type tmp = getUnboxedType((ClassType) t2);
                        if (tmp != null) {
                            t2 = tmp;
                        } else {
                            t1 = getBoxedType((PrimitiveType) t1);
                        }
                    } else if (t1 instanceof ClassType && t2 instanceof PrimitiveType) {
                        Type tmp = getUnboxedType((ClassType) t1);
                        if (tmp != null) {
                            t1 = tmp;
                        } else {
                            t2 = getBoxedType((PrimitiveType) t2);
                        }
                    }
                }
                if (t1 == t2) {
                    result = t1;
                } else if (t1 instanceof PrimitiveType && t2 instanceof PrimitiveType) {
                    NameInfo ni = getNameInfo();
                    if ((t1 == ni.getShortType() && t2 == ni.getByteType())
                            || (t2 == ni.getShortType() && t1 == ni.getByteType())) {
                        result = ni.getShortType();
                    } else {
                        result = serviceConfiguration.getConstantEvaluator()
                                .getCompileTimeConstantType(op);
                        if (result == null) {
                            if (isNarrowingTo(e1, (PrimitiveType) t2)) {
                                return t2;
                            }
                            if (isNarrowingTo(e2, (PrimitiveType) t1)) {
                                return t1;
                            }
                            result = getPromotedType((PrimitiveType) t1, (PrimitiveType) t2);
                        }
                    }
                } else if (t1 instanceof PrimitiveType || t2 instanceof PrimitiveType) {
                    getErrorHandler().reportError(
                        new TypingException("Incompatible types in conditional", op));
                    result = getNameInfo().getUnknownType();
                } else { // two reference types
                    if (t1 == getNameInfo().getNullType()) {
                        result = t2; // null x T --> T
                    } else if (t2 == getNameInfo().getNullType()) {
                        result = t1; // T x null --> T
                    } else {
                        if (isWidening(t1, t2)) {
                            result = t2;
                        } else if (isWidening(t2, t1)) {
                            result = t1;
                        } else {
                            if (java5Allowed() && t1 instanceof ClassType
                                    && t2 instanceof ClassType) {
                                // intersection type allowed since java 5.
                                List<Type> tml = new ArrayList<>(getAllSupertypes((ClassType) t1));
                                List<? extends ClassType> comp = getAllSupertypes((ClassType) t2);
                                for (int j = tml.size() - 1; j >= 0; j--) {
                                    if (!comp.contains(tml.get(j))) {
                                        tml.remove(j);
                                    }
                                }
                                removeSupertypesFromList(tml);
                                if (tml.size() == 0) {
                                    throw new Error(); // why is java.lang.Object not found ?
                                }
                                if (tml.size() == 1) {
                                    result = tml.get(0);
                                } else {
                                    result = new IntersectionType(tml, this);
                                }
                            } else {
                                getErrorHandler().reportError(
                                    new TypingException("Incompatible types in conditional", op));
                                result = getNameInfo().getUnknownType();
                            }
                        }
                    }
                }
            } else {
                Debug.error(
                    "Type resolution not implemented for operation " + op.getClass().getName());
            }
        } else if (expr instanceof Literal) { ///////////////// Literals
            if (expr instanceof NullLiteral) {
                result = getNameInfo().getNullType();
            } else if (expr instanceof BooleanLiteral) {
                result = getNameInfo().getBooleanType();
            } else if (expr instanceof LongLiteral) {
                result = getNameInfo().getLongType();
            } else if (expr instanceof IntLiteral) {
                result = getNameInfo().getIntType();
            } else if (expr instanceof FloatLiteral) {
                result = getNameInfo().getFloatType();
            } else if (expr instanceof DoubleLiteral) {
                result = getNameInfo().getDoubleType();
            } else if (expr instanceof CharLiteral) {
                result = getNameInfo().getCharType();
            } else if (expr instanceof StringLiteral) {
                result = getNameInfo().getJavaLangString();
            }
        } else if (expr instanceof Reference) { ///////////////// References
            if (expr instanceof UncollatedReferenceQualifier) {
                result = getType((UncollatedReferenceQualifier) expr);
            } else if (expr instanceof MetaClassReference) {
                result = getNameInfo().getJavaLangClass();
            } else if (expr instanceof VariableReference) {
                // look for the variable declaration
                Variable v = getVariable((VariableReference) expr);
                if (v != null) {
                    result = v.getType();
                    if (expr instanceof FieldReference) {
                        Type t = getType(((FieldReference) expr).getReferencePrefix());
                        if (t instanceof ParameterizedType && containsTypeParameter(result)) {
                            result = replaceTypeParameter((ParameterizedType) t, result).baseType;
                        }
                        // handle "implicit" type parameters which occur on type
                        // declarations such as
                        // class A extends ArrayList<String> { }
                        // TODO think if this can be handled more efficently!
                        if (t instanceof ClassType && containsTypeParameter(result)) {
                            List<? extends ClassType> allSupertypes =
                                ((ClassType) t).getAllSupertypes();
                            for (int i = 1 /* skip type itself */; i < allSupertypes.size(); i++) {
                                ClassType st = allSupertypes.get(i);
                                if (st instanceof ParameterizedType) {
                                    result = replaceTypeParameter((ParameterizedType) st,
                                        result).baseType;
                                    if (!containsTypeParameter(result)) {
                                        break; // done
                                    }
                                }
                            }
                        }
                    }
                } else {
                    getErrorHandler().reportError(new UnresolvedReferenceException(
                        Format.toString("Could not resolve " + ELEMENT_LONG, expr) + " (01)",
                        expr));
                    v = getNameInfo().getUnknownField();
                }

            } else if (expr instanceof MethodReference) {
                // look for the return type of the method
                Method m = getMethod((MethodReference) expr);
                if (m != null) {
                    result = m.getReturnType();
                    if (containsTypeParameter(result) && m.getTypeParameters() != null
                            && m.getTypeParameters().size() != 0) {
                        // may need type inferrence
                        for (int i = 0; i < m.getTypeParameters().size(); i++) {
                            TypeParameter currentTypeParam = m.getTypeParameters().get(i);
                            MethodReference mr = (MethodReference) expr;
                            Type replacement = null;
                            if (mr.getTypeArguments() != null) {
                                // 1) explicit generic invocation
                                TypeArgumentDeclaration ta = mr.getTypeArguments().get(i);
                                replacement = getType(ta.getTypeReferenceAt(0));
                                if (ta.getTypeArguments() != null) {
                                    replacement = new ParameterizedType((ClassType) replacement,
                                        replaceTypeParameter(ta.getTypeArguments(),
                                            currentTypeParam, (ClassType) replacement));
                                }
                            } else {
                                // 2) type inferrence
                                replacement = inferType(m, mr, currentTypeParam.getName());
                            }
                            List<? extends TypeArgument> typeArgs = null;
                            if (result instanceof ParameterizedType) {
                                typeArgs = ((ParameterizedType) result).getTypeArgs();
                                typeArgs = replaceTypeParameter(typeArgs, currentTypeParam,
                                    (ClassType) replacement);
                                result = ((ParameterizedType) result).getGenericType();
                            }
                            if (result == currentTypeParam) {
                                result = replacement;
                            }
                            if (typeArgs != null) {
                                result = new ParameterizedType((ClassType) result, typeArgs);
                            }
                        }
                    }
                    MethodReference mr = (MethodReference) expr;
                    if (mr.getReferencePrefix() != null) {
                        Type t = getType(mr.getReferencePrefix());

                        if (t instanceof ParameterizedType && containsTypeParameter(result)) {
                            result = replaceTypeParameter((ParameterizedType) t, result).baseType;
                        }
                        // handle "implicit" type parameters which occur on type declarations such
                        // as
                        // class A extends ArrayList<String> { }
                        // TODO think if this can be handled more efficently!
                        if (t instanceof ClassType && containsTypeParameter(result)) {
                            List<? extends ClassType> allSupertypes =
                                ((ClassType) t).getAllSupertypes();
                            for (int i = 1 /* skip type itself */; i < allSupertypes.size(); i++) {
                                ClassType st = allSupertypes.get(i);
                                if (st instanceof ParameterizedType) {
                                    result = replaceTypeParameter((ParameterizedType) st,
                                        result).baseType;
                                    if (!containsTypeParameter(result)) {
                                        break; // done
                                    }
                                }
                            }
                        }
                    }
                }
            } else if (expr instanceof AnnotationPropertyReference) {
                AnnotationProperty ap = getAnnotationProperty((AnnotationPropertyReference) expr);
                if (ap != null) {
                    result = ap.getReturnType();
                }
            } else if (expr instanceof ArrayLengthReference) {
                result = getNameInfo().getIntType();
            } else if (expr instanceof ArrayReference) {
                ArrayReference aref = (ArrayReference) expr;
                Type ht = getType(aref.getReferencePrefix());
                if (ht != null && !(ht instanceof UnknownClassType)) {
                    List<Expression> dimExprs = aref.getDimensionExpressions();
                    int dims = dimExprs.size();
                    for (int i = 0; i < dims; i++) {
                        ht = ((ArrayType) ht).getBaseType();
                    }
                    if (ht != null) {
                        result = ht;
                    } else {
                        getErrorHandler().reportError(new TypingException(
                            "Not an array type: " + ht + " in expression " + expr, expr));
                        result = getNameInfo().getUnknownType();
                    }
                }
            } else if (expr instanceof ThisReference) {
                ReferencePrefix rp = ((ThisReference) expr).getReferencePrefix();
                if (rp == null) {
                    result = getContainingClassType(expr);
                } else {
                    // the prefix "points" to the required type...
                    result = getType(rp);
                }
            } else if (expr instanceof SuperReference) {
                ReferencePrefix rp = ((SuperReference) expr).getReferencePrefix();
                ClassType thisType;
                if (rp == null) {
                    thisType = getContainingClassType(expr);
                } else {
                    thisType = (ClassType) getType(rp);
                }
                List<ClassType> supers = thisType.getSupertypes();
                if ((supers != null) && (!supers.isEmpty())) {
                    result = supers.get(0);
                }
            }
        } else if (expr instanceof ArrayInitializer) { //// ArrayInitializer
            ProgramElement pe = expr;
            while ((pe != null) && !(pe instanceof VariableSpecification)
                    && !(pe instanceof NewArray)) {
                pe = pe.getASTParent();
            }
            result = getType(pe);
        } else if (expr instanceof ElementValueArrayInitializer) {
            ProgramElement pe = expr;
            while ((pe != null) && !(pe instanceof VariableSpecification)) {
                pe = pe.getASTParent();
            }
            result = getType(pe);
        } else if (expr instanceof AnnotationUseSpecification) {
            result = getType(((AnnotationUseSpecification) expr).getTypeReference());
        } else {
            Debug.error("Type analysis for general expressions is currently not implemented: "
                + expr + " <" + expr.getClass().getName() + ">");
        }
        return result;
    }

    private Type inferType(Method m, MethodReference mr, String typeParamName) {
        List<Type> result = new ArrayList<>();
        List<Type> sig = m.getSignature();
        for (int j = 0; j < sig.size(); j++) {
            // look at all parameters
            Type t = sig.get(j);
            Expression e = mr.getArguments().get(j);
            Type actualArgType = getType(e);

            inferType1(typeParamName, result, t, actualArgType);
        }
        removeSupertypesFromList(result);
        if (result.size() == 0) {
            // if raw types were used, java.lang.Object may not have been inferred
            return getNameInfo().getJavaLangObject();
        } else if (result.size() == 1) {
            return result.get(0);
        } else {
            return new IntersectionType(result, getServiceConfiguration().getImplicitElementInfo());
        }
    }

    /**
     * removes every type from the list if any of its subtypes is on the list, too
     *
     * @param result
     * @return
     */
    private void removeSupertypesFromList(List<Type> result) {
        // now, remove everything that is redundant
        for (int j = result.size() - 1; j >= 0; j--) {
            for (int k = 0; k < result.size() - 1; k++) {
                Type a = result.get(j);
                Type b = result.get(k);
                if (a instanceof ArrayType) {
                    assert b instanceof ArrayType;
                    // assert dimensions are equal ?
                    while (a instanceof ArrayType) {
                        a = ((ArrayType) a).getBaseType();
                        b = ((ArrayType) b).getBaseType();
                    }
                }
                if (isSupertype((ClassType) a, (ClassType) b)) {
                    result.remove(j);
                    break; // continue with outer loop
                }
            }
        }
    }

    private void inferType1(String typeParamName, List<Type> result, Type t, Type actualArgType) {
        inferType2(typeParamName, result, t, actualArgType);
        if (t instanceof ParameterizedType && actualArgType instanceof ParameterizedType) {
            // also consider type arguments
            ParameterizedType tp = (ParameterizedType) t;
            ParameterizedType ap = (ParameterizedType) actualArgType;
            for (int i = 0; i < tp.getTypeArgs().size(); i++) {
                inferType1(typeParamName, result, getBaseType(tp.getTypeArgs().get(i)),
                    getBaseType(ap.getTypeArgs().get(i)));
            }
        }
    }

    private void inferType2(String typeParamName, List<Type> result, Type t, Type actualArgType) {
        Type toAdd = actualArgType;
        int reduceDim = 0;
        while (t instanceof ArrayType) {
            t = ((ArrayType) t).getBaseType();
            reduceDim++;
        }
        if (t instanceof TypeParameter && t.getName().equals(typeParamName)) {
            while (reduceDim > 0) {
                toAdd = ((ArrayType) toAdd).getBaseType();
                reduceDim--;
            }
            List<? extends Type> ctl = new ArrayList<ClassType>();
            int dim = 0;
            if (toAdd instanceof ArrayType) {
                // special handling needed: go to base type, collect supertypes, then create array
                // types
                while (toAdd instanceof ArrayType) {
                    toAdd = ((ArrayType) toAdd).getBaseType();
                    dim++;
                }
                ctl = getAllSupertypes((ClassType) toAdd);
                List<Type> tmp = new ArrayList<>(ctl.size());
                for (Type type : ctl) {
                    tmp.add(getNameInfo().createArrayType(type, dim));
                }
                ctl = tmp;
            } else {
                ctl = getAllSupertypes((ClassType) toAdd); // ClassCastException => invalid source
                                                           // code (primitive type)
            }
            if (result.isEmpty()) {
                // first match: add all; at least java.lang.Object will retain in list afterwards
                result.addAll(ctl);
            } else {
                // intersect the two lists ("retainAll")
                for (int i = result.size() - 1; i >= 0; i--) {
                    if (!ctl.contains(result.get(i))) {
                        result.remove(i);
                    }
                }
            }
        }
    }

    private List<TypeArgument> replaceTypeParameter(List<? extends TypeArgument> typeArgs,
            TypeParameter typeParam, ClassType replacement) {
        List<TypeArgument> res = new ArrayList<>();
        for (TypeArgument ta : typeArgs) {
            TypeArgument newTa = ta;
            List<? extends TypeArgument> newTas = null;
            if (ta.getTypeArguments() != null) {
                newTas = replaceTypeParameter(ta.getTypeArguments(), typeParam, replacement);
            }
            if (getBaseType(ta) == typeParam) {
                newTa = new ResolvedTypeArgument(ta.getWildcardMode(), replacement, newTas);
            } else if (newTas != null) {
                newTa = new ResolvedTypeArgument(ta.getWildcardMode(), getBaseType(ta), newTas);
            }
            res.add(newTa);
        }
        return res;
    }

    // TODO one of many hacks...
    public /* private!! */ boolean containsTypeParameter(Type t) {
        while (t instanceof ArrayType) {
            t = ((ArrayType) t).getBaseType();
        }
        if (!(t instanceof ClassType)) {
            return false;
        }
        if (t instanceof TypeParameter) {
            return true;
        }
        if (t instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) t;
            if (pt.getGenericType() instanceof TypeParameter) {
                return true;
            }
            for (TypeArgument ta : pt.getTypeArgs()) {
                if (containsTypeParameter(ta)) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean containsTypeParameter(TypeArgument ta) {
        if (getBaseType(ta) instanceof TypeParameter) {
            return true;
        }
        if (ta.getTypeArguments() != null) {
            for (TypeArgument nta : ta.getTypeArguments()) {
                if (containsTypeParameter(nta)) {
                    return true;
                }
            }
        }
        return false;
    }

    private List<? extends TypeArgument> replaceTypeArgsRec(ParameterizedType context,
            List<? extends TypeArgument> targs) {
        List<TypeArgument> result = new ArrayList<>(targs.size());
        for (TypeArgument ta : targs) {
            Type ct = getBaseType(ta);
            ReplaceTypeArgResult repl = replaceTypeParameter(context, ct);
            result.add(new ResolvedTypeArgument(repl.wildcardMode, repl.baseType,
                repl.baseType instanceof ParameterizedType
                        ? ((ParameterizedType) repl.baseType).getTypeArgs()
                        : null));
        }
        return result;
    }

    // TODO the field wildcardMode of return type is needed for recursive call only !!!!
    private ReplaceTypeArgResult replaceTypeParameter(ParameterizedType context, Type toReplace) {
        ReplaceTypeArgResult result;
        List<? extends TypeArgument> newTypeArgs = null;
        if (toReplace instanceof ArrayType) {
            ArrayType arrayType = (ArrayType) toReplace;
            ReplaceTypeArgResult innerResult =
                replaceTypeParameter(context, arrayType.getBaseType());
            result =
                new ReplaceTypeArgResult(getNameInfo().createArrayType(innerResult.baseType), null);
            return result;
        }
        if (toReplace instanceof ParameterizedType) {
            // TODO if entering this branch, a lot of senseless object creation may occur
            // if nothing needs to be actually done...
            ParameterizedType pt = (ParameterizedType) toReplace;
            newTypeArgs = replaceTypeArgsRec(context, pt.getTypeArgs());
            toReplace = pt.getGenericType();
        }
        result = new ReplaceTypeArgResult(toReplace, null);
        if (toReplace instanceof TypeParameter) {
            result = super.replaceTypeArg(toReplace, context.getTypeArgs(),
                context.getGenericType().getTypeParameters());
        }
        if (newTypeArgs != null) {
            result = new ReplaceTypeArgResult(
                new ParameterizedType((ClassType) result.baseType, newTypeArgs),
                result.wildcardMode);
        }
        return result;
    }

    public boolean isNarrowingTo(Expression expr, PrimitiveType to) {
        NameInfo ni = getNameInfo();
        int minValue, maxValue;
        if (to == ni.getByteType()) {
            minValue = Byte.MIN_VALUE;
            maxValue = Byte.MAX_VALUE;
        } else if (to == ni.getCharType()) {
            minValue = Character.MIN_VALUE;
            maxValue = Character.MAX_VALUE;
        } else if (to == ni.getShortType()) {
            minValue = Short.MIN_VALUE;
            maxValue = Short.MAX_VALUE;
        } else {
            return false;
        }
        ConstantEvaluator ce = serviceConfiguration.getConstantEvaluator();
        ConstantEvaluator.EvaluationResult res = new ConstantEvaluator.EvaluationResult();
        if (!ce.isCompileTimeConstant(expr, res)
                || res.getTypeCode() != ConstantEvaluator.INT_TYPE) {
            return false;
        }
        int value = res.getInt();
        return (minValue <= value) && (value <= maxValue);
    }

    public Type getType(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        // updateModel(); not necessary
        Type result = null;
        if (pme instanceof Type) {
            result = (Type) pme;
        } else {
            if (pme instanceof ProgramElement) {
                result = getType((ProgramElement) pme);
                if ((result == null) && (pme instanceof VariableSpecification)) {
                    if (pme instanceof EnumConstantSpecification) {
                        // this would mean an enum constant specification outside an enum, which
                        // shouldn't be possible to construct (syntax error)
                        throw new IllegalStateException(
                            "Enum constant outside an enum, this shouldn't even be possible");
                    }
                    // void is acceptable for method decls
                    getErrorHandler().reportError(new UnresolvedReferenceException(
                        Format.toString("Unknown type of " + ELEMENT_LONG, pme),
                        (((VariableSpecification) pme).getParent()).getTypeReference()));
                    result = getNameInfo().getUnknownType();
                }
                if (result == null && pme instanceof EnumConstantDeclaration) {
                    // this can't happen!
                    throw new Error(
                        "fatal error: EnumConstantDeclaration occured outside enum declaration");
                }
            } else {
                result = pme.getProgramModelInfo().getType(pme);
            }
        }
        return result;
    }

    public ClassType getContainingClassType(ProgramElement context) {
        Debug.assertNonnull(context);
        // updateModel(); not necessary
        if (context instanceof TypeDeclaration) {
            context = context.getASTParent();
        }
        do {
            if (context instanceof ClassType) {
                return (ClassType) context;
            }
            context = context.getASTParent();
        } while (context != null);
        return null;
    }

    public ClassType getContainingClassType(Member m) {
        Debug.assertNonnull(m);
        // updateModel(); not necessary
        ClassType result = null;
        ProgramElement pe = getDeclaration(m);
        if (pe == null) {
            result = m.getProgramModelInfo().getContainingClassType(m);
        } else {
            result = getContainingClassType(pe);
        }
        return result;
    }

    /*
     * Returns a field with the given name from the given class type or from the bottommost
     * supertype that defines it.
     */
    protected Field getInheritedField(String name, ClassType ct) {
        // for private use only - no model update required
        List<? extends Field> fl = ct.getAllFields();
        int nf = fl.size();
        for (Field f : fl) {
            if (name.equals(f.getName())) {
                return f;
            }
        }
        return null;
    }

    /*
     * context can make a difference under rare circumstances a context before a local declaration
     * will not locate the declaration and will look for a variable in an outer scope
     */
    public Variable getVariable(String name, ProgramElement context) {
        ProgramElement originalContext = context;
        Debug.assertNonnull(name, context);
        updateModel();
        if (DEBUG) {
            Debug.log("Looking for variable " + name);
        }
        // special case handling for java 5 first:
        if (java5Allowed()
                && (context instanceof VariableReference
                        || context instanceof UncollatedReferenceQualifier)
                && context.getASTParent() instanceof Case && getType(((Case) context.getASTParent())
                        .getParent().getExpression()) instanceof EnumDeclaration) {
            /*
             * is it an enum constant? Possible iff: 1) parent is "case" 2) switch-selector is an
             * enum type (that way, the selector specifies the scope!)
             */
            EnumConstantSpecification ecs = (EnumConstantSpecification) ((EnumDeclaration) getType(
                ((Case) context.getASTParent()).getParent().getExpression()))
                        .getVariableInScope(name);
            // must not resolve! qualifying enum constant in case-statements is forbidden!
            return ecs;
        }

        // look for the next variable scope equals to or parent of context
        ProgramElement pe = context;
        while (pe != null && !(pe instanceof VariableScope)) {
            context = pe;
            pe = pe.getASTParent();
        }
        if (DEBUG) {
            Debug.log("Found scope " + Format.toString("%c @%p", pe));
        }
        if (pe == null) {
            // a null scope can happen if we try to find a variable
            // speculatively (for URQ resolution)
            return null;
        }
        VariableScope scope = (VariableScope) pe;
        Variable result;
        do {
            result = scope.getVariableInScope(name);
            if (result != null) {
                if (DEBUG) {
                    Debug.log("Found variable in scope " + Format.toString("%c @%p", scope));
                }

                // must double check this result - rare cases of confusion
                // involving field references before a local variable of the
                // same name has been specified
                if (scope instanceof StatementBlock) {
                    StatementContainer cont = (StatementBlock) scope;
                    // we need the topmost var-scope including context,
                    // or context itself if the found scope is the topmost one
                    // typecast to VariableDeclaration is safe, as result cannot be EnumConstant
                    VariableDeclaration def = ((VariableSpecification) result).getParent();
                    for (int i = 0; true; i += 1) {
                        Statement s = cont.getStatementAt(i);
                        if (s == def) {
                            // Debug.log(">>> Not ignored: " +
                            // Format.toString("%c \"%s\" @%p", result) + " for
                            // context " + Format.toString("@%p", context));

                            // stop if definition comes first
                            break;
                        }
                        if (s == context) {
                            // tricky: reference before definition - must
                            // ignore the definition :(

                            // Debug.log(">>> Ignored: " + Format.toString("%c
                            // \"%s\" @%p", result) + " for context " +
                            // Format.toString("@%p", context));
                            result = null;
                            break;
                        }
                    }
                }
                if (result != null) {
                    // leave _now_
                    break;
                }
            }
            if (scope instanceof TypeDeclaration) {
                result = getInheritedField(name, (TypeDeclaration) scope);
                if (result != null) {
                    break;
                }
                // might want to check for ambiguity of outer class fields!!!
            }
            pe = scope.getASTParent();
            while (pe != null && !(pe instanceof VariableScope)) {
                context = pe; // proceed the context
                pe = pe.getASTParent();
            }
            scope = (VariableScope) pe;
        } while (scope != null);

        // last chance: field imported through static import?
        if (result == null && java5Allowed()) {
            List<Import> imports = UnitKit.getCompilationUnit(context).getImports();
            ClassType ct = MiscKit.getParentTypeDeclaration(originalContext);
            result = getVariableFromStaticSingleImport(name, imports, ct);
            if (result == null) // try on demand
            {
                result = getVariableFromStaticOnDemandImport(name, imports, ct);
            }
        }
        return result;
    }

    private Variable getVariableFromStaticSingleImport(String name, List<Import> imports,
            ClassType context) {
        Variable result = null;
        Variable oldResult = null;
        Import firstImport = null; // for error handling only
        for (Import imp : imports) {
            if (!imp.isStaticImport() || imp.isMultiImport()) {
                continue;
            }
            // has import correct name?
            if (!name.equals(imp.getStaticIdentifier().getText())) {
                continue;
            }
            // try to get field from this type's context.
            List<? extends Field> fields = getFields((ClassType) getType(imp.getTypeReference()));
            // see if any visible field matches
            for (Field field : fields) {
                if (!field.getName().equals(name)) {
                    continue;
                }
                if (isVisibleFor(field, context)) {
                    result = field;
                    if (oldResult != null && oldResult != result) {
                        // Ambiguity
                        getErrorHandler().reportError(new AmbiguousStaticFieldImportException(
                            firstImport, imp, oldResult, result));
                        // go on if neccessary
                    }
                    firstImport = imp;
                    oldResult = field;
                    break; // maximum of one match per import
                }

            }
        }
        return result;
    }

    private Variable getVariableFromStaticOnDemandImport(String name, List<Import> imports,
            ClassType context) {
        Debug.assertNonnull(name);
        Debug.assertNonnull(imports);
        Debug.assertNonnull(context);
        Variable result = null;
        Variable oldResult = null;
        Import firstImport = null; // for error handling only
        for (Import imp : imports) {
            if (!imp.isStaticImport() || !imp.isMultiImport()) {
                continue;
            }
            // try to get field from this type's context.
            List<? extends Field> fields = getFields((ClassType) getType(imp.getTypeReference()));
            // see if any visible field matches
            for (Field field : fields) {
                if (!field.getName().equals(name)) {
                    continue;
                }
                if (isVisibleFor(field, context)) {
                    result = field;
                    if (oldResult != null && oldResult != result) {
                        // Ambiguity
                        getErrorHandler().reportError(new AmbiguousStaticFieldImportException(
                            firstImport, imp, oldResult, result));
                        // go on if neccessary
                    }
                    firstImport = imp;
                    oldResult = field;
                    break; // maximum of one match per import
                }

            }
        }
        return result;
    }

    public final Variable getVariable(VariableSpecification vs) {
        return vs;
    }

    public Field getField(FieldReference fr) {
        Field res = (Field) reference2element.get(fr);
        if (res != null) {
            return res;
        }
        updateModel();
        String name = fr.getName();
        ReferencePrefix rp = fr.getReferencePrefix();
        if (rp == null) {
            res = (Field) getVariable(name, fr);
            if (res != null) {
                reference2element.put(fr, res);
            }
            return res;
        } else {
            ClassType thisType = getContainingClassType(fr);
            if (thisType == null) {
                return null;
            }
            ClassType ct = (ClassType) getType(rp);
            if (ct == null || ct instanceof UnknownClassType) {
                return null;
            }
            List<? extends Field> fl = ct.getAllFields();
            if (fl == null) {
                return null;
            }
            for (int i = fl.size() - 1; i >= 0; i--) {
                res = fl.get(i);
                if (res.getName() == name) {
                    reference2element.put(fr, res);
                    return res;
                }
            }
            return null;
        }
    }

    public Variable getVariable(VariableReference vr) {
        if (vr instanceof FieldReference) {
            return getField((FieldReference) vr);
        } else {
            Variable res = (Variable) reference2element.get(vr);
            if (res != null) {
                return res;
            }
            res = getVariable(vr.getName(), vr);
            if (res != null) {
                reference2element.put(vr, res);
            }
            return res;
        }
    }

    // args == null is admissible
    public List<Type> makeSignature(List<Expression> args) {
        if (args == null || args.isEmpty()) {
            return new ArrayList<>(0);
        }
        // updateModel(); not necessary
        int arity = args.size();
        List<Type> result = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
            Expression e = args.get(i);
            Type et = getType(e);
            if (et == null) {
                getErrorHandler().reportError(new TypingException("Unknown type for argument #" + i
                    + " in call " + Format.toString(ELEMENT_LONG, e.getExpressionContainer()), e));
                et = getNameInfo().getUnknownType();
            }
            result.add(et);
        }
        return result;
    }

    public final Method getMethod(MethodDeclaration md) {
        return md;
    }

    public final Constructor getConstructor(ConstructorDeclaration cd) {
        return cd;
    }

    /**
     * UNTESTED AND INCOMPLETE
     *
     * @param pe
     * @return
     */
    private final String isAppropriate(Method m, MethodReference mr) {
        // follows JLS ?15.12.3
        // TODO
        if (mr.getReferencePrefix() == null) {
            return m.isStatic() || !occursInStaticContext(mr) ? null
                    : "method invocation to non-static method occurs in static context (a)";
        }
        if (mr.getReferencePrefix() instanceof TypeReference && !m.isStatic()) {
            // static access to a nun-static member
            return "Static access to a non-static member";
        }
        if (mr.getTypeReferenceCount() == 1) {
            // access path is static, so method must be static, too
            // TODO this may also be a reference to an outer type, so this check is removed for now!
            // return m.isStatic() ? null : "method invocation to non-static method occurs in static
            // context (b)";
            return null;
        }
        if (mr.getReferencePrefix() instanceof SuperReference) {
            SuperReference sr = (SuperReference) mr.getReferencePrefix();
            if (m.isAbstract()) {
                // System.out.println(m.getContainingClassType().getFullName());
                // return "cannot access super method because it is abstract";
                // TODO this one may trigger a bug if an interfaces re-declares methods from
                // java.lang.Object,
                // e.g. public object clone()
            }
            if (occursInStaticContext(mr)) {
                return "method invocation to non-static method occurs in static context (c)";
            }
            if (sr.getReferencePrefix() != null
                    && (sr.getReferencePrefix() instanceof TypeReference)) {
                // TODO
                /*
                 * "Let C be the class denoted by ClassName. If the invocation is not directly
                 * enclosed by C or an inner class of C, then a compile-time error occurs"
                 */
            }
            return null;
        }
        if (mr.getReferenceSuffix() != null && m.getReturnType() == null) {
            return "void method must not have a reference suffix";
        }
        return null;
    }

    private final boolean occursInStaticContext(MethodReference mr) {
        ProgramElement pe = mr;
        while (pe != null) {
            if (pe instanceof ClassInitializer) {
                return ((ClassInitializer) pe).isStatic();
            }
            if (pe instanceof MethodDeclaration) {
                return ((MethodDeclaration) pe).isStatic();
            }
            if (pe instanceof FieldDeclaration) {
                return ((FieldDeclaration) pe).isStatic();
            }
            pe = pe.getASTParent();
        }
        // this only happens if parent links aren't set properly
        getErrorHandler().reportError(new ModelException("cannot determine if MethodReference "
            + Format.toString(pe) + " occurs in static context; check parent links!"));
        return false;
    }

    public AnnotationProperty getAnnotationProperty(AnnotationPropertyReference apr) {
        AnnotationProperty res = (AnnotationProperty) reference2element.get(apr);
        if (res != null) {
            return res;
        }
        Type at = getType(apr.getParent().getParent().getTypeReference());
        if (at instanceof ClassType && ((ClassType) at).isAnnotationType()) {
            ClassType ct = (ClassType) at;
            List<? extends Method> ml = ct.getMethods();
            for (Method method : ml) {
                if (method.getName().equals(apr.getIdentifier().getText())) {
                    // TODO check for ambiguities (which mean invalid code)
                    // TODO better exception if it's actually a method and not an annotation
                    // property?
                    res = (AnnotationProperty) method;
                    break;
                }
            }
            if (res == null) {
                getErrorHandler().reportError(new UnresolvedReferenceException(
                    Format.toString("Could not resolve " + ELEMENT_LONG + " (12)", apr), apr));
                res = getNameInfo().getUnknownAnnotationProperty();
            }
        } else {
            if (at == null) {
                getErrorHandler().reportError(new UnresolvedReferenceException(
                    Format.toString("Could not resolve " + ELEMENT_LONG + " (13)", apr), apr));
            } else {
                getErrorHandler().reportError(new ModelException(Format
                        .toString(ELEMENT_LONG + " does not reference an annotation type!", apr)));
                res = getNameInfo().getUnknownAnnotationProperty();
            }
        }
        reference2element.put(apr, res);
        return res;
    }

    public Method getMethod(MethodReference mr) {
        Method res = (Method) reference2element.get(mr);
        if (res != null) {
            return res;
        }
        List<? extends Method> mlist = getMethods(mr);
        if (mlist == null || mlist.isEmpty()) {
            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + " (02)", mr), mr));
            return getNameInfo().getUnknownMethod();
        } else if (mlist.size() > 1) {
            getErrorHandler().reportError(new AmbiguousReferenceException(
                Format.toString(ELEMENT_LONG + " is ambiguous - it could be one of ", mr)
                        + Format.toString("%N", mlist),
                mr, mlist));
            // if we have to resume, use the first for the time being
        } else {
            String msg;
            if ((msg = isAppropriate(mlist.get(0), mr)) != null) {
                getErrorHandler()
                        .reportError(new UnresolvedReferenceException(
                            Format.toString(
                                "Inappropriate method access: " + msg + " at " + ELEMENT_LONG, mr),
                            mr));
            }
        }
        res = mlist.get(0);
        reference2element.put(mr, res);
        return res;
    }

    public List<Method> getMethods(MethodReference mr) {
        Debug.assertNonnull(mr);
        updateModel();
        List<Method> result = null;
        List<Type> signature = makeSignature(mr.getArguments());
        ReferencePrefix rp = mr.getReferencePrefix();
        if (rp == null) {
            ClassType targetClass = getContainingClassType(mr);
            result = getMethods(targetClass, mr.getName(), signature, mr.getTypeArguments());
            // if we didn't find an adequate method - the target class may be
            // an inner or anonymous class. So we have to look "outside"
            if (result != null && result.size() > 0) {
                return result;
            }
            for (ClassTypeContainer ctc = targetClass.getContainer(); ctc != null; ctc =
                ctc.getContainer()) {
                if (ctc instanceof ClassType) {
                    result =
                        getMethods((ClassType) ctc, mr.getName(), signature, mr.getTypeArguments());
                    if ((result != null) && (result.size() > 0)) {
                        return result;
                    }
                }
            }
            // If java 5 is supported, check if an appropriate method is imported through a static
            // import
            if (java5Allowed()) {
                List<Import> imports = UnitKit.getCompilationUnit(mr).getImports();
                result = getMethodsFromStaticSingleImports(mr, imports);
                if (result != null && result.size() > 0) {
                    return result;
                }
                result = getMethodsFromStaticOnDemandImports(mr, imports);
                if (result != null && result.size() > 0) {
                    return result;
                }
            }


            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + " (03)", mr), mr));
            List<Method> list = new ArrayList<>(1);
            list.add(getNameInfo().getUnknownMethod());
            result = list;
        } else {
            Type rpt = getType(rp);
            if (rpt == null) {
                // TODO: voidMethod().illegal reports that voidMethod() cannot be resolved although
                // it exists and a more specific error message should occur
                getErrorHandler().reportError(new UnresolvedReferenceException(
                    Format.toString("Could not resolve " + ELEMENT_LONG + " (04)", rp), rp));
                List<Method> list = new ArrayList<>(1);
                list.add(getNameInfo().getUnknownMethod());
                return list;
            }
            if (rpt instanceof ArrayType) {
                rpt = getNameInfo().getJavaLangObject();
            }
            result = getMethods((ClassType) rpt, mr.getName(), signature, mr.getTypeArguments());
        }
        return result;
    }

    /**
     * @param mr
     * @param imports
     * @return
     */
    private List<Method> getMethodsFromStaticOnDemandImports(MethodReference mr,
            List<Import> imports) {
        NameInfo ni = getNameInfo();
        List<Method> result = new ArrayList<>();
        for (Import imp : imports) {
            if (!imp.isStaticImport() || !imp.isMultiImport()) {
                continue;
            }
            List<? extends Method> ml =
                ni.getClassType(Naming.toPathName(imp.getTypeReference())).getMethods();
            for (Method m : ml) {
                // is method static and has matching name?
                if (m.isStatic() && m.getName().equals(mr.getName())) {
                    result.add(m);
                }
            }
        }
        List<Type> sig = makeSignature(mr.getArguments());
        return doThreePhaseFilter(result, sig, mr.getName(), MiscKit.getParentTypeDeclaration(mr),
            mr.getTypeArguments());
    }

    /**
     * traverses all single static import declaration and looks for appropriate methods.
     *
     * @param mr
     * @param imports
     * @return
     * @throws AmbiguousImportException if there are any ambiguities
     */
    private List<Method> getMethodsFromStaticSingleImports(MethodReference mr,
            List<Import> imports) {
        NameInfo ni = getNameInfo();
        List<Method> result = new ArrayList<>();
        for (Import imp : imports) {
            if (!imp.isStaticImport() || imp.isMultiImport()) {
                continue;
            }
            // is import applicable?
            if (!imp.getStaticIdentifier().getText().equals(mr.getName())) {
                continue;
            }
            List<? extends Method> ml =
                ni.getClassType(Naming.toPathName(imp.getTypeReference())).getMethods();
            for (Method m : ml) {
                // is method static and has matching name? (This is also checked again later)
                if (m.isStatic() && m.getName().equals(mr.getName())) {
                    result.add(m);
                }
                // Could remove duplicates here (imports may be listed twice), but that's
                // autoamtically done
                // by first pass of filterMostSpecificMethods()
            }
        }
        List<Type> sig = makeSignature(mr.getArguments());
        return doThreePhaseFilter(result, sig, mr.getName(), MiscKit.getParentTypeDeclaration(mr),
            mr.getTypeArguments());
    }

    public Constructor getConstructor(ConstructorReference cr) {
        Constructor res = (Constructor) reference2element.get(cr);
        if (res != null) {
            return res;
        }
        List<? extends Constructor> clist = getConstructors(cr);
        if (clist == null || clist.isEmpty()) {
            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + " (05)", cr), cr));
            return getNameInfo().getUnknownConstructor();
        } else if (clist.size() > 1) {
            getErrorHandler().reportError(new AmbiguousReferenceException(
                Format.toString(ELEMENT_LONG + " is ambiguous - it could be one of ", cr)
                        + Format.toString("%N", clist),
                cr, clist));
            // use the first, if we do have to continue
        }
        res = clist.get(0);
        reference2element.put(cr, res);
        return res;
    }

    public List<? extends Constructor> getConstructors(ConstructorReference cr) {
        updateModel();
        ClassType type = null;
        if (cr instanceof New) {
            New n = (New) cr;
            ReferencePrefix rp = n.getReferencePrefix();
            if (rp != null) {
                // In this case we need not do anything
            }
            type = (ClassType) getType(n.getTypeReference());
        } else if (cr instanceof ThisConstructorReference) {
            type = getContainingClassType(cr);
        } else if (cr instanceof SuperConstructorReference) {
            type = getContainingClassType(cr);
            List<? extends ClassType> superTypes = getSupertypes(type);
            for (ClassType superType : superTypes) {
                type = superType;
                if (!type.isInterface()) {
                    break; // there must be one concrete class
                    // the exception would be parsing a super() call inside
                    // java.lang.Object ;)
                }
            }
        } else if (cr instanceof EnumConstructorReference) {
            type = getContainingClassType(cr);
        } else {
            Debug.error("Unknown Constructor Reference " + cr);
        }
        if (type == null) {
            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + " (06)", cr), cr));
            List<Constructor> list = new ArrayList<>(1);
            list.add(getNameInfo().getUnknownConstructor());
            return list;
        }
        return getConstructors(type, makeSignature(cr.getArguments()));
    }

    public List<TypeDeclaration> getTypes(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        List<MemberDeclaration> members = td.getMembers();
        if (members == null) {
            return new ArrayList<>(0);
        }
        int s = members.size();
        List<TypeDeclaration> result = new ArrayList<>();
        for (MemberDeclaration m : members) {
            if (m instanceof TypeDeclaration) {
                result.add((TypeDeclaration) m);
            }
        }
        return result;
        // was: td.getTypesInScope(); -- faster, but not order preserving
    }

    public List<FieldSpecification> getFields(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        List<MemberDeclaration> members = td.getMembers();
        if (members == null) {
            return new ArrayList<>(0);
        }
        int s = members.size();
        List<FieldSpecification> result = new ArrayList<>();
        for (MemberDeclaration m : members) {
            if (m instanceof FieldDeclaration) {
                result.addAll(((FieldDeclaration) m).getFieldSpecifications());
            } else if (m instanceof EnumConstantDeclaration) {
                result.add(((EnumConstantDeclaration) m).getEnumConstantSpecification());
            }
        }
        return result;
        // was: td.getFieldsInScope(); -- faster, but not order preserving
    }

    public List<Method> getMethods(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        List<MemberDeclaration> members = td.getMembers();
        if (members == null && !(td instanceof EnumDeclaration)) {
            return new ArrayList<>(0);
        }
        int s = (members == null) ? 0 : members.size();
        List<Method> result = new ArrayList<>();
        for (int i = 0; i < s; i += 1) {
            MemberDeclaration m = members.get(i);
            if (m instanceof MethodDeclaration) {
                if (!(m instanceof ConstructorDeclaration)) {
                    result.add((MethodDeclaration) m);
                }
            }
        }
        if (td instanceof EnumDeclaration) {
            List<ImplicitEnumMethod> rl = serviceConfiguration.getImplicitElementInfo()
                    .getImplicitEnumMethods((EnumDeclaration) td);
            result.add(rl.get(0));
            result.add(rl.get(1));
        }
        return result;
    }

    public List<Constructor> getConstructors(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        List<Constructor> result = new ArrayList<>(2);
        List<MemberDeclaration> members = td.getMembers();
        int s = (members == null) ? 0 : members.size();
        for (int i = 0; i < s; i += 1) {
            MemberDeclaration m = members.get(i);
            if (m instanceof ConstructorDeclaration) {
                result.add((ConstructorDeclaration) m);
            }
        }
        if (result.isEmpty() && !td.isInterface() && td.getName() != null) {
            result.add(serviceConfiguration.getImplicitElementInfo().getDefaultConstructor(td));
        }
        return result;
    }

    public Package getPackage(PackageReference pr) {
        Package res = (Package) reference2element.get(pr);
        if (res != null) {
            return res;
        }
        res = getNameInfo().createPackage(Naming.toPathName(pr));
        if (res != null) {
            reference2element.put(pr, res);
        }
        return res;
    }

    public Package getPackage(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        updateModel();
        Package result = null;
        ProgramElement pe = getDeclaration(pme);
        if (pe == null) {
            result = pme.getProgramModelInfo().getPackage(pme);
        } else {
            result =
                getNameInfo().createPackage(Naming.getPackageName(UnitKit.getCompilationUnit(pe)));
        }
        return result;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        Debug.assertNonnull(ctc);
        updateModel();
        ProgramElement decl = getDeclaration(ctc);
        if (decl == null) {
            return ctc.getProgramModelInfo().getTypes(ctc);
        } else {
            while (decl != null && !(decl instanceof TypeScope)) {
                decl = decl.getASTParent();
            }
            Debug.assertNonnull(decl, "Internal error - scope inconsistency");
            return ((TypeScope) decl).getTypesInScope();
        }
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        Debug.assertNonnull(ct);
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            return ct.getProgramModelInfo().getClassTypeContainer(ct);
        }
        // updateModel(); not necessary
        ProgramElement cur = td;
        NonTerminalProgramElement par = cur.getASTParent();
        while (par != null) {
            cur = par;
            if (cur instanceof ClassTypeContainer) {
                return (ClassTypeContainer) cur;
            }
            par = cur.getASTParent();
        }
        return getNameInfo().createPackage(Naming.getPackageName((CompilationUnit) cur));
    }

    List<ClassType> getTypeList(List<TypeReference> trl) {
        updateModel();
        int s = (trl != null) ? trl.size() : 0;
        List<ClassType> result = new ArrayList<>(s);
        for (int i = 0; i < s; i++) {
            result.add((ClassType) getType(trl.get(i)));
        }
        return result;
    }

    void addToTypeList(ArrayList<ClassType> result, List<TypeReference> trl) {
        // updateModel();
        int s = (trl != null) ? trl.size() : 0;
        result.ensureCapacity(result.size() + s);
        for (int i = 0; i < s; i++) {
            TypeReference tr = trl.get(i);
            if (tr != null) {
                ClassType ct = (ClassType) getType(tr);
                if (ct == null) {
                    getErrorHandler().reportError(new UnresolvedReferenceException(
                        Format.toString("Unable to resolve " + ELEMENT_LONG, tr), tr));
                    ct = getNameInfo().getUnknownClassType();
                }
                result.add(ct);
            }
        }
    }

    public List<ClassType> getSupertypes(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            return ct.getProgramModelInfo().getSupertypes(ct);
        } else {
            ClassTypeCacheEntry ctce = classTypeCache.get(ct);
            if (ctce == null) {
                classTypeCache.put(ct, ctce = new ClassTypeCacheEntry());
            }
            if (ctce.supertypes != null) {
                return ctce.supertypes;
            }
            ArrayList<ClassType> res = new ArrayList<>();
            if (td instanceof EnumDeclaration) {
                // only java.lang.Enum and java.lang.Object
                res.add(getNameInfo().getJavaLangEnum());
                res.add(getNameInfo().getJavaLangObject());
            } else if (td instanceof AnnotationDeclaration) {
                // only java.lang.annotation.Annotation and java.lang.Object
                res.add(getNameInfo().getJavaLangAnnotationAnnotation());
                res.add(getNameInfo().getJavaLangObject());
            } else if (td instanceof InterfaceDeclaration) {
                InterfaceDeclaration id = (InterfaceDeclaration) td;
                Extends ext = id.getExtendedTypes();
                if (ext != null) {
                    addToTypeList(res, ext.getSupertypes());
                }
                res.add(getNameInfo().getJavaLangObject());
            } else if (td instanceof TypeParameterDeclaration) {
                TypeParameterDeclaration tp = (TypeParameterDeclaration) td;
                if (tp.getBounds() == null || tp.getBounds().size() == 0) {
                    // see JLS 3rd edition ?4.4
                    res.add(getNameInfo().getJavaLangObject());
                } else {
                    for (TypeReference tr : tp.getBounds()) {
                        // res.add((ClassType) getType(tr));
                        String name = tr.getName();
                        if (tr.getReferencePrefix() != null) {
                            name = Naming.toPathName(tr.getReferencePrefix(), name);
                        }
                        res.add((ClassType) getType(name, tp.getASTParent()));
                    }
                }
            } else {
                ClassDeclaration cd = (ClassDeclaration) td;

                // Anonymous classes need special care
                TypeDeclarationContainer con = cd.getParent();
                if (con instanceof New) {
                    TypeReference tr = ((New) con).getTypeReference();
                    res.add((ClassType) getType(tr));
                } else {
                    Extends ext = cd.getExtendedTypes();
                    if (ext != null) {
                        addToTypeList(res, ext.getSupertypes());
                    }
                    Implements imp = cd.getImplementedTypes();
                    if (imp != null) {
                        addToTypeList(res, imp.getSupertypes());
                    }
                }
                if (res.isEmpty()) {
                    ClassType jlo = getNameInfo().getJavaLangObject();
                    if (ct != jlo) {
                        res.add(jlo);
                    }
                }
            }
            return ctce.supertypes = res;
        }
    }

    public List<? extends Field> getFields(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        List<? extends Field> result = null;
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            result = ct.getProgramModelInfo().getFields(ct);
        } else {
            result = getFields(td);
        }
        return result;
    }

    public List<Method> getMethods(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        List<Method> result = null;
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            result = ct.getProgramModelInfo().getMethods(ct);
        } else {
            result = getMethods(td);
        }
        return result;
    }

    public List<? extends Constructor> getConstructors(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        List<? extends Constructor> result = null;
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            result = ct.getProgramModelInfo().getConstructors(ct);
        } else {
            result = getConstructors(td);
        }
        return result;
    }

    public List<Type> getSignature(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        List<Type> result = new ArrayList<>(0);
        MethodDeclaration md = getMethodDeclaration(m);
        if (md == null) {
            result = m.getProgramModelInfo().getSignature(m);
        } else {
            List<ParameterDeclaration> pdl = md.getParameters();
            int params = (pdl == null) ? 0 : pdl.size();
            if (params > 0) {
                ArrayList<Type> res = new ArrayList<>(params);
                result = res;
                for (int i = 0; i < params; i++) {
                    Type ptype = getType(pdl.get(i).getVariables().get(0));
                    res.add(ptype);
                }
            }
        }
        return result;
    }

    public List<ClassType> getExceptions(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        List<ClassType> result = new ArrayList<>(0);
        MethodDeclaration md = getMethodDeclaration(m);
        if (md == null) {
            result = m.getProgramModelInfo().getExceptions(m);
        } else {
            Throws t = md.getThrown();
            if (t != null) {
                result = getTypeList(t.getExceptions());
            }
        }
        return result;
    }

    public Type getReturnType(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        Type result = null;
        MethodDeclaration md = getMethodDeclaration(m);
        if (md == null) {
            result = m.getProgramModelInfo().getReturnType(m);
        } else {
            TypeReference tr = md.getTypeReference();
            if (tr != null && !"void".equals(tr.getName())) {
                result = getType(tr);
            }
        }
        return result;
    }

    public Type getAnnotationType(AnnotationUseSpecification au) {
        Debug.assertNonnull(au);
        updateModel();
        Type result = null;
        TypeReference tr = au.getTypeReference();
        if (tr != null) { // TODO what if tr == null? That'd be wrong...
            result = getType(tr);
        }
        return result;
    }

    public Reference resolveURQ(UncollatedReferenceQualifier urq) {
        NonTerminalProgramElement parent = urq.getASTParent();
        return resolveURQ(urq,
            !((parent instanceof TypeReference) || (parent instanceof PackageReference)));
    }

    protected Reference resolveURQ(UncollatedReferenceQualifier urq, boolean allowVariables) {
        Debug.assertNonnull(urq);
        ReferencePrefix rp = urq.getReferencePrefix();
        if (rp instanceof UncollatedReferenceQualifier) {
            rp = (ReferencePrefix) resolveURQ((UncollatedReferenceQualifier) rp, allowVariables);
        }
        updateModel();
        Reference result = null;
        NameInfo ni = getNameInfo();
        NonTerminalProgramElement parent = urq.getASTParent();
        String urqName = urq.getName();

        if (rp == null) {
            if (allowVariables) {
                // is it a variable?
                Variable v = getVariable(urqName, urq);
                if (v != null) {
                    result =
                        (v instanceof Field) ? urq.toFieldReference() : urq.toVariableReference();
                    reference2element.put(result, v);
                }
            }
            /*
             * else if (parent instanceof MethodReference) { // this case is common enough for
             * special treatment result = urq.toTypeReference(); }
             */
            if (result == null) {
                // is the URQ a reference to an already known package?
                Package pkg = ni.getPackage(urqName);
                if (pkg != null) {
                    result = urq.toPackageReference();
                    reference2element.put(result, pkg);
                } else {
                    // the urq might only be either a type or a package ref
                    Type t = getType(urqName, urq);
                    if (t != null) {
                        result = urq.toTypeReference();
                        reference2element.put(result, t);
                    } else if (urqName.charAt(0) >= 'A' && urqName.charAt(0) <= 'Z') {
                        // assume coding conventions were followed! There is no other
                        // means of telling what this is at this time...
                        result = urq.toTypeReference();
                        // unknown type...
                        getErrorHandler().reportError(new UnresolvedReferenceException(
                            Format.toString("Could not resolve " + ELEMENT_LONG + " (07b)", urq),
                            urq));
                    } else {
                        // should be a reference to an unknown package
                        // however, this can also be something else, but once again,
                        // we can't tell...
                        try {
                            result = urq.toPackageReference();
                        } catch (ClassCastException cce) {
                            getErrorHandler().reportError(new UnresolvedReferenceException(
                                Format.toString("Could not resolve " + ELEMENT_LONG + " (07)", urq),
                                urq));
                            result = urq.toTypeReference();
                        }
                    }
                }
            }
        } else if (rp instanceof ThisReference) {
            // the URQ can only be a local inner type or an attribute
            TypeScope thisScope;
            ReferencePrefix rpp = ((ThisReference) rp).getReferencePrefix();
            if (rpp == null) {
                thisScope = (TypeScope) getContainingClassType(urq);
            } else {
                TypeReference tr = (rpp instanceof TypeReference) ? (TypeReference) rpp
                        : (TypeReference) resolveURQ((UncollatedReferenceQualifier) rpp, false);
                thisScope = (TypeDeclaration) getType(tr);
            }
            Variable v = getVariable(urqName, thisScope);
            if (v != null) {
                result = urq.toFieldReference();
                reference2element.put(result, v);
            } else {
                // the URQ is either a type reference or invalid
                Type refT = thisScope.getTypeInScope(urqName);
                if (refT != null) {
                    result = urq.toTypeReference();
                    reference2element.put(result, refT);
                }
            }
        } else if (rp instanceof SuperReference) {
            // the URQ can only be an inner type or a field reference
            ClassType superType = (ClassType) getType(rp);
            Field f = getInheritedField(urq.getName(), superType);
            if (f != null) {
                result = urq.toFieldReference();
                reference2element.put(result, f);
            } else {
                String fullname = Naming.getFullName(superType, urq.getName());
                ClassType ct = ni.getClassType(fullname);
                if (ct != null) {
                    result = urq.toTypeReference();
                    reference2element.put(result, ct);
                }
            }
        } else if (rp instanceof PackageReference) {
            String fullRefName = Naming.toPathName(urq);
            // is the URQ a reference to an already known package?
            Package pkg = ni.getPackage(fullRefName);
            if (pkg != null) {
                result = urq.toPackageReference();
                reference2element.put(result, pkg);
            } else {
                // is it a type?
                Type t = ni.getClassType(fullRefName);
                if (t != null) {
                    result = urq.toTypeReference();
                    reference2element.put(result, t);
                } else {
                    // if the reference suffix is a method/constructor or field reference, then this
                    // must be an unknown type.
                    if (urq.getReferenceSuffix() instanceof MethodReference || (allowVariables
                            && urq.getReferenceSuffix() instanceof FieldReference)) {
                        result = urq.toTypeReference();
                    } else {
                        // this should be a package reference otherwise.
                        // we can't really say, so we will regard it as a package reference and
                        // cope with some special handling later
                        result = urq.toPackageReference();
                    }
                }
            }
        } else if ((rp instanceof TypeReference) || (rp instanceof Expression)) {
            // includes VariableReferences
            Type refT = getType(rp);
            if (refT instanceof ClassType) {
                ClassType ct = (ClassType) refT;
                if (allowVariables) {
                    Field f = getInheritedField(urq.getName(), ct);
                    if (f != null) {
                        result = urq.toFieldReference();
                        reference2element.put(result, f);
                    }
                }
                if (result == null) {
                    String fullname = Naming.getFullName((ClassType) refT, urq.getName());
                    ClassType innerType = ni.getClassType(fullname);
                    if (innerType != null) {
                        result = urq.toTypeReference();
                        reference2element.put(result, innerType);
                    }
                }
            } else if (refT instanceof ArrayType) {
                if (allowVariables && urq.getName() == "length") {
                    result = urq.toArrayLengthReference();
                } else {
                    getErrorHandler().reportError(new UnresolvedReferenceException(
                        Format.toString("Could not resolve " + ELEMENT_LONG + " (08)", urq), urq));
                    // this IS an error in any case, but so what
                    result = urq;
                }
            } else {
                getErrorHandler().reportError(new UnresolvedReferenceException(
                    Format.toString("Could not resolve " + ELEMENT_LONG + " (09)", rp), rp));
                // this would have been a class or a field
                result = urq;
            }
        } else {
            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + " (10)", rp), rp));
            // this would have been a class or a field or a package
            result = urq;
        }
        if (result == null) {
            getErrorHandler().reportError(new UnresolvedReferenceException(
                Format.toString("Could not resolve " + ELEMENT_LONG + " (11)", urq), urq));
            result = urq;
        } else if (result != urq) {
            try {
                parent.replaceChild(urq, result);
            } catch (ClassCastException cce) {
                /*
                 * If guessed wrong before further up in this method about wether something unknown
                 * was a package, type, or field reference, this (hopefully) corrects that bad
                 * guess. This special case arises if a field to an unknown type, or a not existing
                 * field to a known type is referenced in an expression. We now can at least make
                 * another guess.
                 */

                boolean throwAgain = true;
                if (!(result instanceof Expression)) {
                    if (result instanceof PackageReference) {
                        PackageReference pr = (PackageReference) result;
                        ProgramFactory pf = result.getFactory();
                        Package pack =
                            pf.getServiceConfiguration().getNameInfo().getPackage(pr.toSource());
                        if (pack == null) {
                            PackageReference pkgToBeReplacedByType = pr.getPackageReference();
                            PackageReference newPr = null;
                            TypeReference typeRef = null;
                            if (pkgToBeReplacedByType != null) {
                                newPr = pr.getPackageReference().getPackageReference();
                                typeRef = pf.createTypeReference(newPr,
                                    pkgToBeReplacedByType.getIdentifier());
                            }
                            result = pf.createFieldReference(typeRef, pr.getIdentifier());
                            result.setStartPosition(pr.getStartPosition());
                            result.setEndPosition(pr.getEndPosition());
                            result.setRelativePosition(pr.getRelativePosition());
                            result.setComments(pr.getComments());
                            throwAgain = false;
                            parent.replaceChild(urq, result);
                        }
                    }
                }
                if (throwAgain) {
                    throw cce;
                }
            }
            Debug.assertBoolean(parent == result.getASTParent());
        }
        return result;
    }

    private boolean java5Allowed() {
        return serviceConfiguration.getProjectSettings().java5Allowed();
    }

    public List<Statement> getSucceedingStatements(Statement s) {
        List<Statement> list = new ArrayList<>();
        if (s instanceof LoopStatement) {
            LoopStatement loop = (LoopStatement) s;
            switch (getBooleanStatus(loop.getGuard())) {
            case CONSTANT_TRUE:
                if (loop.getBody() != null) {
                    list.add(loop.getBody());
                }
                break;
            case CONSTANT_FALSE:
                if (loop.isCheckedBeforeIteration()) {
                    // while, for
                    addSequentialFollower(s, list);
                } else {
                    // do
                    if (loop.getBody() != null) {
                        list.add(loop.getBody());
                    }
                    addSequentialFollower(s, list);
                }
                break;
            case NOT_CONSTANT:
                if (loop.getBody() != null) {
                    list.add(loop.getBody());
                }
                addSequentialFollower(s, list);
                break;
            }
        } else if (s instanceof LabeledStatement) {
            list.add(((LabeledStatement) s).getBody());
        } else if (s instanceof StatementBlock) {
            List<Statement> slist = ((StatementBlock) s).getBody();
            if (slist == null || slist.isEmpty()) {
                addSequentialFollower(s, list);
            } else {
                list.add(slist.get(0));
            }
        } else if (s instanceof SynchronizedBlock) {
            List<Statement> slist = ((SynchronizedBlock) s).getBody().getBody();
            if (slist == null || slist.isEmpty()) {
                addSequentialFollower(s, list);
            } else {
                list.add(slist.get(0));
            }
        } else if (s instanceof If) {
            If ifstmt = (If) s;
            if (ifstmt.getElse() != null) {
                list.add(ifstmt.getThen().getBody());
                list.add(ifstmt.getElse().getBody());
            } else {
                list.add(ifstmt.getThen().getBody());
                addSequentialFollower(s, list);
            }
        } else if (s instanceof Switch) {
            List<Branch> branches = ((Switch) s).getBranchList();
            if (branches == null || branches.isEmpty()) {
                addSequentialFollower(s, list);
            } else {
                boolean hasDefault = false;
                for (int i = 0, c = branches.size(); i < c; i += 1) {
                    Branch b = branches.get(i);
                    List<Statement> stats = null;
                    if (b instanceof Default) {
                        stats = ((Default) b).getBody();
                        if (i < c - 1 || (stats != null && !stats.isEmpty())) {
                            // an empty default as last branch is not
                            // significant
                            hasDefault = true;
                        }
                    } else if (b instanceof Case) {
                        stats = ((Case) b).getBody();
                    }
                    if (stats != null && !stats.isEmpty()) {
                        list.add(stats.get(0));
                    }
                }
                if (!hasDefault) {
                    addSequentialFollower(s, list);
                }
            }
        } else if (s instanceof Try) {
            list.add(((Try) s).getBody());
            List<Branch> branches = ((Try) s).getBranchList();
            if (branches == null || branches.isEmpty()) {
                addSequentialFollower(s, list);
                return list;
            }
            for (int i = 0; i < branches.size(); i += 1) {
                Branch b = branches.get(i);
                if (b instanceof Catch) {
                    Catch ca = (Catch) b;
                    boolean newException = true;
                    if (i > 0) {
                        ClassType ex =
                            (ClassType) getType(ca.getParameterDeclaration().getTypeReference());
                        for (int j = i - 1; j >= 0; j -= 1) {
                            if (branches.get(j) instanceof Catch) {
                                ClassType dx = (ClassType) getType(((Catch) branches.get(j))
                                        .getParameterDeclaration().getTypeReference());
                                if (isSubtype(ex, dx)) {
                                    // exception was already caught
                                    newException = false;
                                    break;
                                }
                            }
                        }
                    }
                    if (newException) {
                        list.add(ca.getBody());
                    }
                } else if (b instanceof Finally) {
                    list.add(((Finally) b).getBody());
                }
            }
            addSequentialFollower(s, list);
        } else if (s instanceof ExpressionJumpStatement) {
            // Return, Throw
            list.add(METHOD_EXIT);
        } else if (s instanceof Break) {
            if (((Break) s).getIdentifier() == null) {
                addSequentialFollower(findInnermostBreakBlock(s), list);
            } else {
                addSequentialFollower(StatementKit.getCorrespondingLabel((Break) s), list);
            }
        } else if (s instanceof Continue) {
            if (((Continue) s).getIdentifier() == null) {
                list.add(findInnermostLoop(s));
            } else {
                list.add(StatementKit.getCorrespondingLabel((Continue) s).getBody());
            }
        } else {
            /*
             * ConstructorReference: EmptyStatement: ExpressionStatement: LoopInitializer:
             * ClassDeclaration: Assert:
             */
            addSequentialFollower(s, list);
        }
        return list;
    }

    private int getBooleanStatus(Expression expr) {
        if (expr == null) { // handle "for(...;;...)" situation
            return CONSTANT_TRUE;
        }
        ConstantEvaluator.EvaluationResult evr = new ConstantEvaluator.EvaluationResult();
        if (serviceConfiguration.getConstantEvaluator().isCompileTimeConstant(expr, evr)) {
            return evr.getBoolean() ? CONSTANT_TRUE : CONSTANT_FALSE;
        }
        return NOT_CONSTANT;
    }

    /**
     * Analyzes the given program subtree. It is required that the tree has consistent parent links;
     * this is done by the parser frontends or by calling make(All)ParentRole(s)Valid(). If the
     * program element is not a CompilationUnit, it must have a valid parent.
     *
     * @param pe the program element to add.
     */
    public void register(ProgramElement pe) {
        Debug.assertNonnull(pe);
        if (pe instanceof CompilationUnit) {
            if (!((CompilationUnit) pe).isDefinedScope()) {
                analyzeProgramElement(pe);
            }
        } else {
            Debug.assertNonnull(pe.getASTParent());
            analyzeProgramElement(pe);
        }
    }

    /**
     * analyzes the given tree element within the specified scope.
     *
     * @param pe the root element of the tree to be analyzed
     */
    private void analyzeProgramElement(ProgramElement pe) {
        Debug.assertNonnull(pe);
        if (pe instanceof CompilationUnit) {
            CompilationUnit cu = (CompilationUnit) pe;
            String packageName = Naming.getPackageName(cu);
            getNameInfo().createPackage(packageName);
        }
        analyzeProgramElement0(pe);
    }

    private void analyzeProgramElement0(ProgramElement pe) {
        if (pe instanceof TerminalProgramElement) {
            return;
        }
        // traversal will continue with the children of this element
        if (pe instanceof ScopeDefiningElement) {
            ((ScopeDefiningElement) pe).setDefinedScope(true);
            if (pe instanceof MethodDeclaration) {
                // also for ConstructorDeclarations
                ((MethodDeclaration) pe).setProgramModelInfo(this);
            } else if (pe instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) pe;
                td.setProgramModelInfo(this);
                String typename = td.getName();
                if (typename != null) {
                    NonTerminalProgramElement parent = pe.getASTParent();
                    // usually, the type scope is just the parent
                    // there are few exceptions, such as labeled or switch
                    // statements
                    while (!(parent instanceof TypeScope)) {
                        parent = parent.getASTParent();
                    }
                    TypeScope scope = (TypeScope) parent;
                    ClassType dup = scope.getTypeInScope(typename);
                    if (dup != null && dup != td) {
                        getErrorHandler()
                                .reportError(new AmbiguousDeclarationException(
                                    "Duplicate declaration of " + Format.toString(ELEMENT_SHORT, td)
                                        + " - was " + Format.toString(ELEMENT_SHORT, dup),
                                    td, dup));
                        // continue anyway, if we have to
                    }
                    scope.addTypeToScope(td, typename);
                    if (DEBUG) {
                        Debug.log(Format.toString("Registering %N", td));
                    }
                    getNameInfo().register(td);
                }
            }
        } else if (pe instanceof VariableSpecification) {
            // also for FieldSpecification
            VariableSpecification vs = (VariableSpecification) pe;
            vs.setProgramModelInfo(this);
            NonTerminalProgramElement parent = vs.getASTParent().getASTParent();
            // usually, the variable scope is the grand parent
            // there are few exceptions, such as labeled or switch statements
            while (!(parent instanceof VariableScope)) {
                parent = parent.getASTParent();
            }
            VariableScope scope = (VariableScope) parent;

            String vname = vs.getName();
            Variable dup = scope.getVariableInScope(vname);
            if (dup != null && dup != vs) {
                getErrorHandler().reportError(new AmbiguousDeclarationException(
                    "Duplicate declaration of " + Format.toString(ELEMENT_SHORT, vs) + " - was "
                        + Format.toString(ELEMENT_SHORT, dup),
                    vs, dup));
                // continue anyway, if we have to resume
            }
            // check if the new variable hides a local variable
            if (!(scope instanceof TypeDeclaration)) {
                for (VariableScope outer =
                    findOuterVariableScope(scope); !(outer instanceof TypeDeclaration); outer =
                        findOuterVariableScope(outer)) {
                    dup = outer.getVariableInScope(vname);
                    if (dup != null) {
                        getErrorHandler().reportError(new AmbiguousDeclarationException(
                            "Hidden local declaration: " + Format.toString(ELEMENT_SHORT, vs)
                                + " - hides " + Format.toString(ELEMENT_SHORT, dup),
                            vs, dup));
                        // resume anyway
                    }
                }
            }
            scope.addVariableToScope(vs);
            if (vs instanceof FieldSpecification) {
                getNameInfo().register((Field) vs);
            }
        }
        NonTerminalProgramElement cont = (NonTerminalProgramElement) pe;
        int childCount = cont.getChildCount();
        for (int i = 0; i < childCount; i++) {
            analyzeProgramElement0(cont.getChildAt(i));
        }
    }

    void unregister(TypeDeclaration td) {
        unregister(td, td.getName());
    }

    /**
     * Remove given type from outer scope, from name info global dictionary, and from subtype list
     * of all known supertypes (if necessary).
     */
    void unregister(TypeDeclaration td, String shortname) {
        if (shortname != null) {
            ((TypeScope) (td.getASTParent())).removeTypeFromScope(shortname);
        }
        getNameInfo().unregisterClassType(td.getFullName());
        ClassTypeCacheEntry ctce = classTypeCache.get(td);
        if (ctce != null) {
            List<? extends ClassType> superTypes = ctce.supertypes;
            if (superTypes != null) {
                for (int i = superTypes.size() - 1; i >= 0; i -= 1) {
                    removeSubtype(td, superTypes.get(i));
                }
            }
        }
    }

    void unregister(VariableSpecification vs) {
        unregister(vs, vs.getName());
    }

    void unregister(VariableSpecification vs, String shortname) {
        ProgramElement pe = vs.getASTParent().getASTParent();
        while (!(pe instanceof VariableScope)) {
            pe = pe.getASTParent();
        }
        ((VariableScope) pe).removeVariableFromScope(shortname);
        if (vs instanceof FieldSpecification) {
            ClassType ct = ((Field) vs).getContainingClassType();
            getNameInfo().unregisterField(Naming.getFullName(ct, shortname));
        }
    }

    /**
     * unregisters the information, that has been computed when registering the given element.
     *
     * @param pe the program element to be unregistered
     */
    void unregister(ProgramElement pe) {
        Debug.assertNonnull(pe);
        if (pe instanceof TypeDeclaration) {
            unregister((TypeDeclaration) pe);
        } else if (pe instanceof VariableSpecification) {
            unregister((VariableSpecification) pe);
        } else if (pe instanceof VariableDeclaration) {
            List<? extends VariableSpecification> vspecs =
                ((VariableDeclaration) pe).getVariables();
            for (int i = vspecs.size() - 1; i >= 0; i -= 1) {
                unregister(vspecs.get(i));
            }
        }
        TreeWalker tw = new TreeWalker(pe);
        while (tw.next()) {
            pe = tw.getProgramElement();
            if (pe instanceof ScopeDefiningElement) {
                flushScopes((ScopeDefiningElement) pe);
            }
        }
    }

    void flushScopes(ScopeDefiningElement sde) {
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        if (sde instanceof TypeScope) {
            List<? extends ClassType> ctl = ((TypeScope) sde).getTypesInScope();
            if (sde instanceof CompilationUnit) {
                // handle special case of top level CU scopes
                // caching known imported types
                // --- should be redone somewhen
                for (int j = ctl.size() - 1; j >= 0; j -= 1) {
                    ClassType ct = ctl.get(j);
                    if ((ct instanceof TypeDeclaration)
                            && ((TypeDeclaration) ct).getASTParent() == sde) {
                        dni.unregisterClassType(ct.getFullName());
                    }
                }
            } else {
                for (int j = ctl.size() - 1; j >= 0; j -= 1) {
                    dni.unregisterClassType(ctl.get(j).getFullName());
                }
            }
        }
        if (sde instanceof TypeDeclaration) {
            List<FieldSpecification> fl = ((TypeDeclaration) sde).getFieldsInScope();
            for (int j = fl.size() - 1; j >= 0; j -= 1) {
                dni.unregisterField(fl.get(j).getFullName());
            }
        }
        sde.setDefinedScope(false);
    }

    public void reset() {
        super.reset();
        reference2element.clear();
        SourceFileRepository sfr = serviceConfiguration.getSourceFileRepository();
        List<CompilationUnit> cul = sfr.getCompilationUnits();
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        dni.unregisterPackages();
        for (int i = cul.size() - 1; i >= 0; i -= 1) {
            CompilationUnit cu = cul.get(i);
            // remove all scopes
            unregister(cu);
            // now rebuild scopes
            analyzeProgramElement(cu);
        }
    }

}
