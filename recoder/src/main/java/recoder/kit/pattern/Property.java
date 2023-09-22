/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.pattern;

import recoder.ModelElement;
import recoder.ModelException;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.convenience.Naming;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.reference.TypeReference;

/**
 * Creates JavaBean compliant setter/getter access methods.
 * <p>
 * Wishlist: - should always make the field private - options for setter/getter for visibility
 * modifier; usually getter should be more public that setter - option to allow insertion of
 * NullPointerException for non-primitive types - option to forbid creation of indexed property
 * methods - create entries for manifest
 */
public class Property implements DesignPattern {

    private final FieldDeclaration field;

    private final MethodDeclaration getter;

    private final MethodDeclaration setter;

    private MethodDeclaration indexedGetter;

    private MethodDeclaration indexedSetter;

    public Property(FieldDeclaration field) {
        if (field == null) {
            throw new NullPointerException();
        }
        this.field = field;
        ProgramFactory factory = field.getFactory();
        TypeReference typeRef = field.getTypeReference();
        String fieldName = field.getVariables().get(0).getName();
        String typeName = typeRef.toString();
        String className = Naming.createClassName(fieldName);
        String source = "public void set" + className + "(" + typeName + " " + fieldName + "){this."
            + fieldName + "=" + fieldName + ";}";
        try {
            setter = factory.parseMethodDeclaration(source);
            source = "public " + typeName + " get" + className + "(){return " + fieldName + ";}";
            getter = factory.parseMethodDeclaration(source);
            if (typeRef.getDimensions() > 0) {
                // cut last "[]"
                typeName = typeName.substring(0, typeName.length() - 2);
                source = "public void set" + className + "(int index, " + typeName + " " + fieldName
                    + ") { this." + fieldName + "[index] = " + fieldName + "; }";
                indexedSetter = factory.parseMethodDeclaration(source);
                source = "public " + typeName + " get" + className + "(int index){return "
                    + fieldName + "[index];}";
                indexedGetter = factory.parseMethodDeclaration(source);
            }
        } catch (ParserException pe) {
            throw new IllegalArgumentException("Input obviously made parsing impossible: " + pe);
        }
    }

    public FieldDeclaration getField() {
        return field;
    }

    public MethodDeclaration getGetter() {
        return getter;
    }

    public MethodDeclaration getSetter() {
        return setter;
    }

    public MethodDeclaration getIndexedGetter() {
        return getter;
    }

    public MethodDeclaration getIndexedSetter() {
        return setter;
    }

    /**
     * Get total number of participants.
     *
     * @return the number of participants.
     */
    public int getParticipantCount() {
        int res = 0;
        if (field != null) {
            res += 1;
        }
        if (getter != null) {
            res += 1;
        }
        if (setter != null) {
            res += 1;
        }
        if (indexedGetter != null) {
            res += 1;
        }
        if (indexedSetter != null) {
            res += 1;
        }
        return res;
    }

    /**
     * Get a participants by its index.
     *
     * @param index an index of a participant.
     * @return the participant.
     * @throws IndexOutOfBoundsException, if the index is not in bounds.
     */
    public ModelElement getParticipantAt(int index) {
        if (field != null) {
            if (index == 0) {
                return field;
            }
            index -= 1;
        }
        if (getter != null) {
            if (index == 0) {
                return getter;
            }
            index -= 1;
        }
        if (setter != null) {
            if (index == 0) {
                return setter;
            }
            index -= 1;
        }
        if (indexedGetter != null) {
            if (index == 0) {
                return indexedGetter;
            }
            index -= 1;
        }
        if (indexedSetter != null) {
            if (index == 0) {
                return indexedSetter;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Checks that at least one getter or one setter is available and that the types of the
     * participants match.
     */
    public void validate() throws ModelException {
        if (setter == null && getter == null) {
            throw new InconsistentPatternException(
                "Properties must have at least a setter or a getter method");
        }
        String gtype = null, stype = null, ftype = null;
        if (getter != null) {
            gtype = getter.getReturnType().getName();
        } else {
            stype = setter.getParameters().get(0).getTypeReference().getName();
        }
        if (field != null) {
            ftype = field.getTypeReference().getName();
        }
        String btype = (gtype == null) ? stype : gtype;
        if ((stype != null && !btype.equals(stype)) || (gtype != null && !btype.equals(gtype))
                || (ftype != null && !btype.equals(ftype))) {
            throw new InconsistentPatternException("Property types do not match!");
        }
        /*
         * Extensions: Should checked indexed access methods, should compare complete type reference
         * path, not only the last part (a returned by getName), or even better check the logical
         * types for equality (as names could be qualified partially).
         */
    }
}
