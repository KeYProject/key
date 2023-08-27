/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

import recoder.ModelException;
import recoder.bytecode.ClassFile;
import recoder.java.CompilationUnit;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

/**
 * A program model element representing packages.
 *
 * @author AL
 * @author RN
 */
public class Package implements ClassTypeContainer {

    private final String name;

    private ProgramModelInfo pmi;

    /**
     * Creates a new package with the given name, organized by the given program model info.
     *
     * @param name the name of the package.
     * @param pmi the program model info responsible for this package.
     */
    public Package(String name, ProgramModelInfo pmi) {
        Debug.assertNonnull(name);
        this.name = name;
        this.pmi = pmi;
    }

    /**
     * Returns the name of this package.
     *
     * @return the name of this package.
     */
    public String getName() {
        return name;
    }

    /**
     * Returns the name of this package.
     *
     * @return the full name of this program model element.
     */
    public String getFullName() {
        return getName();
    }

    /**
     * Returns the instance that can retrieve information about this program model element.
     *
     * @return the program model info of this element.
     */
    public ProgramModelInfo getProgramModelInfo() {
        return pmi;
    }

    /**
     * Sets the instance that can retrieve information about this program model element.
     *
     * @param service the program model info for this element.
     */
    public void setProgramModelInfo(ProgramModelInfo service) {
        this.pmi = service;
    }

    /**
     * Returns the list of class types defined within this ontainer.
     *
     * @return a list of contained class types.
     */
    public List<? extends ClassType> getTypes() {
        return pmi.getTypes(this);
    }

    /**
     * Returns the list of RuntimeInvisibleAnnotations retrieved from package-info.class, or the
     * list of AnnotationUseSpecification retrieved from package-info.java, respectively. Returns
     * <code>null</code> if neither file is present or no package annotations are specified.
     *
     * @return
     * @since 0.80
     */
    public List<? extends AnnotationUse> getPackageAnnotations() {
        CompilationUnit cl = pmi.getServiceConfiguration().getSourceFileRepository()
                .getCompilationUnit(getFullName() + ".package-info");
        if (cl != null) {
            return cl.getPackageSpecification().getAnnotations();
        }
        ClassFile cf = pmi.getServiceConfiguration().getClassFileRepository()
                .getClassFile(getFullName() + ".package-info");
        if (cf != null) {
            return cf.getAnnotations();
        }
        throw new UnsupportedOperationException();
    }

    /**
     * Returns the enclosing package or class type, or method.
     *
     * @return <CODE>null</CODE>.
     */
    public ClassTypeContainer getContainer() {
        return null;
    }

    /**
     * Returns the enclosing package.
     *
     * @return <CODE>null</CODE>.
     */
    public Package getPackage() {
        return this;
    }

    public void validate() throws ModelException {
        // not checked yet
    }
}
