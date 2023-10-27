/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.Import;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.UnitKit;
import recoder.service.CrossReferenceSourceInfo;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

/**
 * Transformation that removes all superfluous import statements from a compilation unit.
 *
 * @author AL
 * @see recoder.kit.UnitKit#getUnnecessaryImports
 * @since 0.71
 */
public class RemoveUnusedImports extends TwoPassTransformation {

    private final List<CompilationUnit> units;

    private final List<Import> imports;

    private final ProgressListenerManager listeners = new ProgressListenerManager(this);

    /**
     * Creates a new transformation object that removes unused import statements from all
     * compilation units in the source file repository.
     *
     * @param sc the service configuration to use.
     */
    public RemoveUnusedImports(CrossReferenceServiceConfiguration sc) {
        this(sc, sc.getSourceFileRepository().getCompilationUnits());
    }

    /**
     * Creates a new transformation object that removes unused import statements.
     *
     * @param sc the service configuration to use.
     * @param cu a compilation unit that shall be stripped of imports.
     */
    public RemoveUnusedImports(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        ArrayList<CompilationUnit> al = new ArrayList<>(1);
        al.add(cu);
        this.units = al;
        imports = new ArrayList<>();
    }

    /**
     * Creates a new transformation object that removes unused import statements.
     *
     * @param sc the service configuration to use.
     * @param list the compilation units that shall be stripped of imports.
     */
    public RemoveUnusedImports(CrossReferenceServiceConfiguration sc, List<CompilationUnit> list) {
        super(sc);
        if (list == null) {
            throw new IllegalArgumentException("Missing units");
        }
        this.units = list;
        imports = new ArrayList<>();
    }

    /**
     * Adds a progress listener for the analysis phase.
     */
    public void addProgressListener(ProgressListener l) {
        listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        listeners.removeProgressListener(l);
    }

    /**
     * Returns {@link #EQUIVALENCE}or {@link #IDENTITY}.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        listeners.fireProgressEvent(0, units.size(), "Checking Imports");
        CrossReferenceSourceInfo xrsi = getCrossReferenceSourceInfo();
        for (int i = 0; i < units.size(); i += 1) {

            imports.addAll(UnitKit.getUnnecessaryImports(xrsi, units.get(i)));
            listeners.fireProgressEvent(i + 1);
        }
        return setProblemReport(imports.isEmpty() ? IDENTITY : EQUIVALENCE);
    }

    /**
     * Removes the unnecessary import statements.
     */
    public void transform() {
        super.transform();
        for (int i = imports.size() - 1; i >= 0; i -= 1) {
            detach(imports.get(i));
        }
    }

    /**
     * Returns the list of redundant imports.
     *
     * @return the list of imports that are/were superfluous.
     */
    public List<Import> getImportList() {
        return imports;
    }

    /**
     * Returns the compilation units.
     *
     * @return the compilation units.
     */
    public List<CompilationUnit> getCompilationUnits() {
        return units;
    }
}
