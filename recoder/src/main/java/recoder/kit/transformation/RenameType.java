/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Constructor;
import recoder.abstraction.Type;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.service.NameInfo;

/**
 * Transformation that renames a type declaration and all known references to that type. The new
 * name should not hide another type in the declaration context.
 * <p>
 * <B>Implementation warning: </B> does not (yet) check vadility of new name in the context.
 *
 * @author AL
 */
public class RenameType extends TwoPassTransformation {

    private final TypeDeclaration type;

    private final String newName;

    private List<TypeReference> refs;

    private List<? extends Constructor> cons;

    /**
     * Creates a new transformation object that renames a type declaration and all known references
     * to that type. The new name should not hide another type in the declaration context.
     *
     * @param sc the service configuration to use.
     * @param type the type declaration to be renamed; may not be <CODE>null
     *                </CODE> and may not be an anonymous type.
     * @param newName the new name for the element; may not be <CODE>null</CODE> and must denote a
     *        valid identifier name.
     */
    public RenameType(CrossReferenceServiceConfiguration sc, TypeDeclaration type, String newName) {
        super(sc);
        if (type == null) {
            throw new IllegalArgumentException("Missing type");
        }
        if (type.getName() == null) {
            throw new IllegalArgumentException("May not rename anonymous types");
        }
        if (newName == null) {
            throw new IllegalArgumentException("Missing name");
        }
        this.type = type;
        this.newName = newName;
    }

    /**
     * Collects all references to the type and all existing array variants, as well as all
     * constructor declarations. Constructor references are not relevant, as they are either
     * nameless (super / this), or contain a type reference already.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        refs = new ArrayList<>();
        if (newName.equals(type.getName())) {
            return setProblemReport(IDENTITY);
        }
        NameInfo ni = getNameInfo();
        refs.addAll(getCrossReferenceSourceInfo().getReferences(type));
        cons = type.getConstructors();
        if (cons == null) {
            cons = new ArrayList<>(0);
        }
        Type atype = ni.getArrayType(type);
        while (atype != null) {
            refs.addAll(getCrossReferenceSourceInfo().getReferences(atype));
            atype = ni.getArrayType(atype);
        }
        return setProblemReport(EQUIVALENCE);
    }

    /**
     * Locally renames the type declaration, all type references and constructors collected in the
     * analyzation phase.
     *
     * @throws IllegalStateException if the analyzation has not been called.
     * @see #analyze()
     */
    public void transform() {
        super.transform();
        ProgramFactory pf = getProgramFactory();
        replace(type.getIdentifier(), pf.createIdentifier(newName));
        for (int i = cons.size() - 1; i >= 0; i -= 1) {
            Constructor con = cons.get(i);
            if (con instanceof ConstructorDeclaration) {
                replace(((ConstructorDeclaration) con).getIdentifier(),
                    pf.createIdentifier(newName));
            }
        }
        for (int i = refs.size() - 1; i >= 0; i -= 1) {
            replace(refs.get(i).getIdentifier(), pf.createIdentifier(newName));
        }
    }
}
