/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Package;
import recoder.abstraction.Type;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Import;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.MethodReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceInfix;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;
import recoder.util.Order;

public class UnitKit {

    private UnitKit() {
        // singleton
    }

    /**
     * Query that returns the compilation unit which the given program element is located in.
     * Returns <CODE>null</CODE>, if the element is <CODE>
     * null</CODE> or not a part of a compilation unit. If the element is already a compilation
     * unit, the element is returned.
     *
     * @param p a program element.
     * @return the compilation unit of the given element, or <CODE>null</CODE>.
     */
    public static CompilationUnit getCompilationUnit(ProgramElement p) {
        while (p != null) {
            if (p instanceof CompilationUnit) {
                return (CompilationUnit) p;
            }
            p = p.getASTParent();
        }
        return null;
    }

    // creates an empty compilation unit in the package of "brother"
    // CompilationUnit createCompilationUnit(CompilationUnit brother)

    private static ClassType getNecessaryImportedType(CrossReferenceSourceInfo xi, Import imp) {
        if (imp.isMultiImport()) {
            return null;
        }
        TypeReference tr = imp.getTypeReference();
        ClassType ct = (ClassType) xi.getType(tr);
        if (ct == null) {
            throw new RuntimeException(
                "No type found for " + Format.toString(Formats.ELEMENT_LONG, tr));
        }
        // there must be at least one reference to this import
        if (TypeKit.getReferences(xi, ct, imp.getASTParent(), false).size() > 1) {
            return ct;
        } else {
            return null;
        }
    }

    private static boolean isNecessaryMultiTypeImport(CrossReferenceSourceInfo xrsi, Import imp,
            Set coveredTypes) {
        if (!imp.isMultiImport()) {
            return false;
        }
        if (imp.isStaticImport()) {
            return true; // TODO Gutzmann
        }
        TypeReferenceInfix ref = imp.getTypeReference();
        CompilationUnit cu = imp.getParent();
        List<? extends ClassType> types;
        if (ref instanceof PackageReference) {
            types = xrsi.getPackage((PackageReference) ref).getTypes();
        } else {
            types = ((ClassType) xrsi.getType((TypeReference) ref)).getTypes();
        }
        boolean result = false;
        for (int j = types.size() - 1; j >= 0 && !result; j -= 1) {
            ClassType ct = types.get(j);
            if (!coveredTypes.contains(ct)) {
                List<TypeReference> refs = TypeKit.getReferences(xrsi, ct, cu, false);
                for (int k = refs.size() - 1; k >= 0; k -= 1) {
                    if (refs.get(k).getASTParent().getASTParent() == cu) {
                        refs.remove(k);
                    }
                }
                result = !refs.isEmpty();
            }
        }
        return result;
    }

    /**
     * Query that finds all unnecessary import specifications in a compilation unit. Single type
     * imports are considered unnecessary if no reference to the imported type occurs in the unit.
     * There might be fully qualified references only, such that the import would be unused in fact,
     * but this does not seem worthwhile to check. A wildcarded import is considered unused if the
     * only types with the given prefixes are imported by corresponding single type imports.
     * <p>
     * Static imports are not considered yet, which is a TODO
     *
     * @param xrsi the cross reference source info to use.
     * @param cu the compilation unit to find unnecessary imports in.
     * @return a list of unnecessary imports in the unit.
     */
    public static List<Import> getUnnecessaryImports(CrossReferenceSourceInfo xrsi,
            CompilationUnit cu) {
        Debug.assertNonnull(xrsi, cu);
        List<Import> il = cu.getImports();
        if (il == null || il.isEmpty()) {
            return new ArrayList<>(0);
        }
        List<Import> removalList = new ArrayList<>();
        Set<ClassType> coveredTypes = new HashSet<>();
        for (Import imp : il) {
            if (imp.isStaticImport()) {
                continue; // TODO
            }
            if (!imp.isMultiImport()) {
                ClassType ct = getNecessaryImportedType(xrsi, imp);
                if (ct != null) {
                    coveredTypes.add(ct);
                } else {
                    removalList.add(imp);
                }
            }
        }
        for (Import imp : il) {
            if (imp.isStaticImport()) {
                continue; // TODO
            }
            if (imp.isMultiImport() && !isNecessaryMultiTypeImport(xrsi, imp, coveredTypes)) {
                removalList.add(imp);
            }
        }
        return removalList;
    }

    /**
     * @deprecated should become a first class transformation.
     */
    @Deprecated
    public static void removeUnusedImports(ChangeHistory ch, CrossReferenceSourceInfo xrsi,
            CompilationUnit cu) {
        Debug.assertNonnull(ch);
        List<Import> removalList = getUnnecessaryImports(xrsi, cu);
        for (int i = removalList.size() - 1; i >= 0; i -= 1) {
            MiscKit.remove(ch, removalList.get(i));
        }
    }

    /**
     * @deprecated should become a fully grown transformation.
     */
    // checks all type references in the types of the given unit
    // that refer to external class types and ensures that these
    // are imported directly. All multi type imports are deleted,
    // as are all single type imports that are not necessary.
    // Static imports are left untouched for now (TODO - Gutzmann)
    @Deprecated
    public static void normalizeImports(ChangeHistory ch, CrossReferenceSourceInfo xrsi,
            CompilationUnit cu, boolean removeMultiTypeImports, boolean removeSingleTypeImports,
            boolean addJavaLangImports, boolean addDefaultPackageImports) {
        Debug.assertNonnull(xrsi, cu);
        // first step: collect all external class types referred to in the unit
        Set<ClassType> importTypes = new HashSet<>();
        Package unitPackage = cu.getPrimaryTypeDeclaration().getPackage();
        TreeWalker tw = new TreeWalker(cu);
        // skip imports and package spec subtrees
        for (int i = cu.getTypeDeclarationCount() - 1; i >= 0; i -= 1) {
            tw.reset(cu.getTypeDeclarationAt(i));
            while (tw.next(TypeReference.class)) {
                TypeReference tr = (TypeReference) tw.getProgramElement();
                Type type = xrsi.getType(tr);
                while (type instanceof ArrayType) {
                    type = ((ArrayType) type).getBaseType();
                }
                if ((type instanceof ClassType)
                        && !((type instanceof TypeDeclaration)
                                && MiscKit.contains(cu, (TypeDeclaration) type))
                        && (addDefaultPackageImports
                                || ((ClassType) type).getPackage() != unitPackage)
                        && (addJavaLangImports || !type.getFullName().startsWith("java.lang."))) {
                    importTypes.add((ClassType) type);
                }
            }
        }

        List<Import> il = cu.getImports();
        int ilsize = (il == null) ? 0 : il.size();

        // now collect all class types that are already imported
        ClassType[] classTypes = new ClassType[ilsize];
        Set<ClassType> importedTypes = new HashSet<>();
        for (int i = ilsize - 1; i >= 0; i -= 1) {
            Import imp = il.get(i);
            if (!imp.isMultiImport()) {
                TypeReference tr = imp.getTypeReference();
                ClassType ct = (ClassType) xrsi.getType(tr);
                classTypes[i] = ct;
                importedTypes.add(ct);
            }
        }

        Set<ClassType> commonTypes = new HashSet<>(importTypes.size());
        commonTypes.addAll(importTypes);
        // commonTypes.intersect(importedTypes);
        commonTypes.retainAll(importedTypes);

        // compute the types that must be imported additionally
        // importTypes.subtract(commonTypes);
        importTypes.removeAll(commonTypes);

        // now find the types that do no longer have to be imported
        // importedTypes.subtract(commonTypes);
        importedTypes.removeAll(commonTypes);

        // now, remove the no longer used imports including all multi imports
        for (int i = ilsize - 1; i >= 0; i -= 1) {
            Import imp = il.get(i);
            if (imp.isStaticImport()) {
                continue; // TODO - Gutzmann
            }
            if ((imp.isMultiImport() && removeMultiTypeImports) || (!imp.isMultiImport()
                    && removeSingleTypeImports && importedTypes.contains(classTypes[i]))) {
                MiscKit.remove(ch, imp);
            }
        }

        // finally, create required single type imports
        for (ClassType ct : importedTypes) {
            appendImport(ch, cu, ct);
        }
    }

    /**
     * Transformation that appends an import specification for the given class type. This method
     * does not check whether the import is needed or redundant.
     *
     * @param ch the change history to notify (may be <CODE>null</CODE>).
     * @param cu the unit to create the import for.
     * @param ct the class type to create the import for.
     * @return the new import.
     * @deprecated should become a fully grown transformation
     */
    @Deprecated
    public static Import appendImport(ChangeHistory ch, CompilationUnit cu, ClassType ct) {
        return appendImport(ch, cu, ct.getFullName());
    }

    /**
     * Transformation that appends an import specification for the given class type. This method
     * does not check whether the import is needed or redundant.
     *
     * @param ch the change history to notify (may be <CODE>null</CODE>).
     * @param cu the unit to create the import for.
     * @param typeName the class type name to create the import for.
     * @return the new import.
     * @deprecated should become a fully grown transformation.
     */
    @Deprecated
    public static Import appendImport(ChangeHistory ch, CompilationUnit cu, String typeName) {
        Debug.assertNonnull(cu, typeName);
        ProgramFactory factory = cu.getFactory();
        TypeReference ref = TypeKit.createTypeReference(factory, typeName);
        Import newImport = factory.createImport(ref, false);
        newImport.makeAllParentRolesValid();
        MiscKit.append(ch, cu, newImport);
        return newImport;
    }

    /**
     * Transformation that ensures that the given class type is known at the given location by
     * importing it on demand. If the type is already known, <CODE>null</CODE> is returned,
     * otherwise the new import specification that imports the type directly.
     *
     * @param ch the change history to report to (may be <CODE>null</CODE>).
     * @param si the source info service.
     * @param typeName the fully qualified name of the type to be known at the unit level.
     * @param context the context in which the type should be known.
     * @return a new import specification as added to the compilation unit, or <CODE>null</CODE> if
     *         no new import was needed.
     * @deprecated needs further testing - use at your own risks
     */
    @Deprecated
    public static Import ensureImport(ChangeHistory ch, SourceInfo si, String typeName,
            ProgramElement context) {
        Debug.assertNonnull(si, typeName, context);
        Debug.assertBoolean(typeName.length() > 0);
        if (si.getType(typeName, context) != null) {
            return null;
        }
        return appendImport(ch, MiscKit.getParentCompilationUnit(context), typeName);
    }

    /**
     * Transformation that ensures that all type references in the given subtree are resolvable by
     * importing the corresponding types on demand.
     *
     * @param ch the change history to report to (may be <CODE>null</CODE>).
     * @param si the source info service.
     * @param root the root element in a subtree containing type references to check.
     * @deprecated needs further testing - use at your own risks
     */
    @Deprecated
    public static void ensureImports(ChangeHistory ch, SourceInfo si, ProgramElement root) {
        Debug.assertNonnull(si, root);
        CompilationUnit cu = MiscKit.getParentCompilationUnit(root);
        TreeWalker tw = new TreeWalker(root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof TypeReference) {
                String name = Naming.toPathName((TypeReference) pe);
                while (name.endsWith("]")) {
                    name = name.substring(0, name.length() - 2);
                }
                Type type = si.getType(name, pe);
                if (type == null) {
                    ensureImport(ch, si, name, cu);
                }
            }
        }
    }

    /**
     * sort imports lexically and insert one blank line between different top level names
     * !!!!!!!!!!!!!!!!!!!! untested !!!!!!!!!!!!!!!
     */
    public static void sortImports(ChangeHistory ch, CompilationUnit cu) {
        Debug.assertNonnull(cu);
        List<Import> il = cu.getImports();
        if (il == null) {
            return;
        }
        final String[] names = new String[il.size()];
        for (int i = 0; i < il.size(); i += 1) {
            Import imp = il.get(i);
            if (imp.isStaticImport() && !imp.isMultiImport()) {
                MethodReference ref = (MethodReference) imp.getReference();
                // TODO Gutzmann - untested!
                names[i] = Naming.toPathName(ref.getReferencePrefix(), "." + ref.getName());
            } else {
                names[i] = Naming.toPathName(imp.getReference());
            }
        }
        for (int i = 1; i < names.length; i += 1) {
            String x = names[i];
            int j = i - 1;
            while (j >= 0 && Order.LEXICAL.greater(names[j], x)) {
                names[j + 1] = names[j];
                j -= 1;
            }
            names[j + 1] = x;
            if (j + 1 != i) {
                Import oldImp = il.get(i);
                il.remove(i);
                il.add(j + 1, oldImp);
                if (ch != null) {
                    ch.detached(oldImp, cu, i);
                    ch.attached(oldImp);
                }
            }
        }
        String prefix = null;
        for (int i = 0; i < names.length; i += 1) {
            String name = names[i];
            int dot = name.indexOf('.');
            String newPrefix = (dot >= 0) ? name.substring(0, dot) : name;
            if (i > 0 && !prefix.equals(newPrefix)) {
                Import imp = il.get(i);
                SourceElement.Position pos = imp.getFirstElement().getRelativePosition();
                if (pos.getLine() == 0) {
                    pos.setLine(1);
                    imp.getFirstElement().setRelativePosition(pos);
                }
            }
            prefix = newPrefix;
        }
    }
}
