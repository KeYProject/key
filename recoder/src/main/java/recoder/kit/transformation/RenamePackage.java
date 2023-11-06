/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Package;
import recoder.java.reference.PackageReference;
import recoder.kit.*;

/**
 * Transformation that renames a package by renaming all known references to that package. The new
 * name should not be used for another package, and the package should not be defined in class files
 * which cannot be transformed.
 *
 * @author AL
 */
public class RenamePackage extends TwoPassTransformation {

    private final Package pkg;

    private final String newName;

    private List<PackageReference> refs;

    /**
     * Creates a new transformation object that renames a package and all references to it. The new
     * name should not conflict with another package.
     *
     * @param sc the service configuration to use.
     * @param pkg the package to be renamed; may not be <CODE>null</CODE>.
     * @param newName the new name for the element; may not be <CODE>null</CODE> and must denote a
     *        valid identifier name.
     */
    public RenamePackage(CrossReferenceServiceConfiguration sc, Package pkg, String newName) {
        super(sc);
        if (pkg == null) {
            throw new IllegalArgumentException("Missing package");
        }
        if (newName == null) {
            throw new IllegalArgumentException("Missing name");
        }
        this.pkg = pkg;
        this.newName = newName;
    }

    /**
     * Collects all references to the package. The rename may fail with a
     * {@link MissingTypeDeclarations}reporting the types without accessible declaration, or a
     * {@link recoder.kit.NameConflict}reporting an already existing package with the given name.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        if (newName.equals(pkg.getName())) {
            refs = new ArrayList<>(0);
            return setProblemReport(IDENTITY);
        }
        Package pkg2 = getNameInfo().getPackage(newName);
        if (pkg2 != null) {
            return setProblemReport(new NameConflict(pkg2));
        }
        List<ClassType> nonTypeDeclarations = PackageKit.getNonSourcePackageTypes(pkg);
        if (!nonTypeDeclarations.isEmpty()) {
            return setProblemReport(new MissingTypeDeclarations(nonTypeDeclarations));
        }
        refs = getCrossReferenceSourceInfo().getReferences(pkg);
        return setProblemReport(EQUIVALENCE);
    }

    /**
     * Locally renames all package references collected in the analyzation phase.
     *
     * @throws IllegalStateException if the analyzation has not been called.
     * @see #analyze()
     */
    public void transform() {
        super.transform();
        Package p = getNameInfo().createPackage(newName);
        PackageReference pr = PackageKit.createPackageReference(getProgramFactory(), p);
        for (int i = refs.size() - 1; i >= 0; i--) {
            PackageReference ref = refs.get(i);
            replace(ref, pr.deepClone());
        }

    }
}
