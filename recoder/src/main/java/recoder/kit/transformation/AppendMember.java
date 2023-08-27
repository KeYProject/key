/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Constructor;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.java.declaration.*;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;

/**
 * Syntactic transformation that adds the given MemberDeclaration to the list in the given
 * TypeDeclaration at a convenient position. No checks for redundancy or vadility are performed,
 * such as allowed modifiers, name ambiguity. The insert position is behind the last occurance of a
 * member of the same type in the type declaration. If there is no matching member, a predefined
 * order of member types is followed: fields - initializers - constructors - methods - member types.
 *
 * @author unknown
 * @deprecated Does not (yet) check ambiguity or conflicts.
 */
@Deprecated
public class AppendMember extends TwoPassTransformation {

    private final boolean isVisible;

    private final TypeDeclaration parent;

    private final MemberDeclaration child;

    private int insertPosition = -1;

    /**
     * Creates a new transformation object that adds the given MemberDeclaration to the list in the
     * given TypeDeclaration at a convenient position.
     *
     * @param sc the service configuration to use.
     * @param isVisible flag indicating if this transformation shall be visible.
     * @param decl the declaration to modify. may not be <CODE>null</CODE> and must denote a valid
     *        identifier name.
     * @param code the modifier to create, encoded using the codes from
     *        {@link recoder.kit.ModifierKit}.
     */
    public AppendMember(CrossReferenceServiceConfiguration sc, boolean isVisible,
            MemberDeclaration child, TypeDeclaration parent) {
        super(sc);
        if (child == null || parent == null) {
            throw new IllegalArgumentException("Missing declaration");
        }
        this.isVisible = isVisible;
        this.child = child;
        this.parent = parent;
    }

    public boolean isVisible() {
        return isVisible;
    }

    /**
     * Finds out where to insert the new member.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        List<MemberDeclaration> mdl = parent.getMembers();
        if (mdl == null) {
            insertPosition = 0;
            return setProblemReport(NO_PROBLEM);
        }
        int lastField = -1;
        int lastInitializer = -1;
        int lastConstructor = -1;
        int lastMethod = -1;
        int lastType = -1;
        for (int i = mdl.size() - 1; i >= 0; i -= 1) {
            MemberDeclaration x = mdl.get(i);
            if (x instanceof FieldDeclaration) {
                lastField = (lastField < 0) ? i : lastField;
            } else if (x instanceof ClassInitializer) {
                lastInitializer = (lastInitializer < 0) ? i : lastInitializer;
            } else if (x instanceof Constructor) {
                lastConstructor = (lastConstructor < 0) ? i : lastConstructor;
            } else if (x instanceof Method) {
                lastMethod = (lastMethod < 0) ? i : lastMethod;
            } else if (x instanceof Type) {
                lastType = (lastType < 0) ? i : lastType;
            }
        }
        if (child instanceof FieldDeclaration) {
            lastInitializer = lastConstructor = lastMethod = lastType = -1;
        } else if (child instanceof ClassInitializer) {
            lastConstructor = lastMethod = lastType = -1;
        } else if (child instanceof ConstructorDeclaration) {
            lastMethod = lastType = -1;
        } else if (child instanceof MethodDeclaration) {
            lastType = -1;
        }
        if (lastType >= 0) {
            insertPosition = lastType + 1;
        } else if (lastMethod >= 0) {
            insertPosition = lastMethod + 1;
        } else if (lastConstructor >= 0) {
            insertPosition = lastConstructor + 1;
        } else if (lastInitializer >= 0) {
            insertPosition = lastInitializer + 1;
        } else if (lastField >= 0) {
            insertPosition = lastField + 1;
        } else {
            insertPosition = 0;
        }
        return setProblemReport(NO_PROBLEM);
    }

    /**
     * Attaches the member at the proper position.
     *
     * @throws IllegalStateException if the analyzation has not been called.
     * @see #analyze()
     */
    public void transform() {
        super.transform();
        attach(child, parent, insertPosition);
    }
}
