/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import recoder.abstraction.ClassType;
import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Field;
import recoder.abstraction.Method;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.PackageSpecification;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.*;
import recoder.util.Debug;

/**
 * Utility class to obtain or transform Identifiers obeying a set of naming conventions. There
 * should be distinguishable Identifiers for features, constants and classes for any given base
 * name.
 * <p>
 * The default Java naming scheme defines lower case first letters for features, upper case first
 * letters for classes, lower case for packages, and upper case for constants (final attributes).
 * <p>
 * Examples: <BR>
 * createFeatureName("HelloWorld").equals("helloWorld") <BR>
 * createClassName("helloWorld").equals("HelloWorld") <BR>
 * createPackageName("HelloWorld").equals("helloworld") <BR>
 * createConstantName("HelloWorld").equals("HELLOWORLD")
 * <p>
 * All methods create new String or Identifier objects.
 *
 * @author AL
 */

public abstract class Naming {

    private final static Set<String> KEYWORDS = new HashSet<>();

    static {
        KEYWORDS.add("abstract");
        KEYWORDS.add("default");
        KEYWORDS.add("if");
        KEYWORDS.add("private");
        KEYWORDS.add("throw");
        KEYWORDS.add("boolean");
        KEYWORDS.add("do");
        KEYWORDS.add("implements");
        KEYWORDS.add("protected");
        KEYWORDS.add("throws");
        KEYWORDS.add("break");
        KEYWORDS.add("double");
        KEYWORDS.add("import");
        KEYWORDS.add("public");
        KEYWORDS.add("transient");
        KEYWORDS.add("byte");
        KEYWORDS.add("else");
        KEYWORDS.add("instanceof");
        KEYWORDS.add("return");
        KEYWORDS.add("try");
        KEYWORDS.add("case");
        KEYWORDS.add("extends");
        KEYWORDS.add("int");
        KEYWORDS.add("short");
        KEYWORDS.add("void");
        KEYWORDS.add("catch");
        KEYWORDS.add("final");
        KEYWORDS.add("interface");
        KEYWORDS.add("static");
        KEYWORDS.add("volatile");
        KEYWORDS.add("char");
        KEYWORDS.add("finally");
        KEYWORDS.add("long");
        KEYWORDS.add("super");
        KEYWORDS.add("while");
        KEYWORDS.add("class");
        KEYWORDS.add("float");
        KEYWORDS.add("native");
        KEYWORDS.add("switch");
        KEYWORDS.add("const");
        KEYWORDS.add("for");
        KEYWORDS.add("new");
        KEYWORDS.add("synchronized");
        KEYWORDS.add("continue");
        KEYWORDS.add("goto");
        KEYWORDS.add("package");
        KEYWORDS.add("this");
        KEYWORDS.add("assert");
    }

    public static boolean hasLowerCaseBegin(String str) {
        return str.length() != 0 && Character.isLowerCase(str.charAt(0));
    }

    public static String makeLowerCaseBegin(String str) {
        return (str.length() == 0) ? str : Character.toLowerCase(str.charAt(0)) + str.substring(1);
    }

    public static boolean hasUpperCaseBegin(String str) {
        return str.length() != 0 && Character.isUpperCase(str.charAt(0));
    }

    public static String makeUpperCaseBegin(String str) {
        return (str.length() == 0) ? str : Character.toUpperCase(str.charAt(0)) + str.substring(1);
    }

    public static String createMemberName(String base) {
        return makeLowerCaseBegin(base);
    }

    public static Identifier createMemberName(Identifier base) {
        String text = base.getText();
        return hasLowerCaseBegin(text) ? base.deepClone()
                : base.getFactory().createIdentifier(makeLowerCaseBegin(text));
    }

    public static String createClassName(String base) {
        return makeUpperCaseBegin(base);
    }

    public static Identifier createClassName(Identifier base) {
        String text = base.getText();
        return hasUpperCaseBegin(text) ? base.deepClone()
                : base.getFactory().createIdentifier(makeUpperCaseBegin(text));
    }

    public static String createPackageName(String base) {
        return base.toLowerCase();
    }

    public static Identifier createPackageName(Identifier base) {
        return base.getFactory().createIdentifier(base.getText().toLowerCase());
        // It would not pay off to check whether base.getText() is already
        // in lower case.
    }

    public static String createConstantName(String base) {
        return base.toUpperCase();

    }

    public static Identifier createConstantName(Identifier base) {
        return base.getFactory().createIdentifier(base.getText().toUpperCase());
    }

    /**
     * Makes a valid system-specific file path name from a logical (dotted) name. For instance,
     * "java.lang" is converted into "java" + File.separatorChar + "lang".
     */
    public static String makeFilename(String logicalName) {
        return logicalName.replace('.', File.separatorChar);
    }

    /**
     * Concatenates two strings with a dot in the middle. Null strings are considered empty. The
     * implementation is faster than the usual "+" translation and slightly faster than StringBuffer
     * operations and it also needs less memory.
     */
    public static String dot(String prefix, String suffix) {
        if (prefix == null) {
            prefix = "";
        }
        if (suffix == null) {
            suffix = "";
        }
        final int plen = prefix.length();
        final int slen = suffix.length();
        final int tlen = plen + slen + 1;
        final char[] buf = new char[tlen];
        buf[plen] = '.';
        prefix.getChars(0, plen, buf, 0);
        suffix.getChars(0, slen, buf, plen + 1);
        return new String(buf, 0, tlen);
        // strange: new String(buf) is MUCH slower. stupid optimizer.
        // unfortunately, there is no way to avoid allocation of three
        // objects, as the String constructors create a new char array
        // each time. Damn.
    }

    /**
     * Returns the name of an array type with the given basename and the given number of dimensions.
     * If dimensions are zero or the basename is null, the basename is returned. Example:
     * <CODE>toArrayTypeName("java.lang.Object",
     * 2)</CODE> yields <CODE>"java.lang.Object[][]"</CODE>.
     */
    public static String toArrayTypeName(String basename, int dimensions) {
        if (dimensions == 0 || basename == null) {
            return basename;
        }
        int len = basename.length();
        char[] buf = new char[len + 2 * dimensions];
        basename.getChars(0, len, buf, 0);
        while (dimensions > 0) {
            buf[len++] = '[';
            buf[len++] = ']';
            dimensions -= 1;
        }
        return new String(buf, 0, len);
    }

    /**
     * Creates the dotted path name for a reference prefix. Returns an empty string if the prefix is
     * not a {@link recoder.java.reference.NameReference}. Appends array brackets if the prefix is a
     * type reference with a dimension > 0.
     *
     * @param ref a reference prefix.
     * @return the dotted representation of the given reference.
     */
    public static String toPathName(ReferencePrefix ref) {
        if (ref instanceof NameReference) {
            int dim = (ref instanceof TypeReference) ? ((TypeReference) ref).getDimensions() : 0;
            int length = ((NameReference) ref).getName().length() + 2 * dim;
            ReferencePrefix rp = ref;
            while (rp instanceof ReferenceSuffix) {
                ReferencePrefix rrp = ((ReferenceSuffix) rp).getReferencePrefix();
                if (rrp == null) {
                    break;
                }
                rp = rrp;
                length += ((NameReference) rp).getName().length() + 1;
            }
            char[] buf = new char[length];
            int i = 0;
            while (rp != ref) {
                String name = ((NameReference) rp).getName();
                int len = name.length();
                name.getChars(0, len, buf, i);
                i += len;
                buf[i++] = '.';
                rp = (ReferencePrefix) rp.getReferenceSuffix();
            }
            String name = ((NameReference) rp).getName();
            int len = name.length();
            name.getChars(0, len, buf, i);
            i += len;
            while (dim > 0) {
                buf[i++] = '[';
                buf[i++] = ']';
                dim -= 1;
            }
            return new String(buf, 0, length);
        }
        return "";
    }

    /**
     * Creates the dotted path name for a reference prefix and appends a suffix string. Returns the
     * suffix if the prefix is not a {@link recoder.java.reference.NameReference}. Ignores the
     * suffix if it is <CODE>null</CODE> or empty. Assumes that the prefix is not a type reference
     * with a dimension > 0.
     *
     * @param ref a reference prefix.
     * @param suffix a suffix string.
     * @return the dotted representation of the given reference and the suffix.
     * @since 0.72
     */
    public static String toPathName(ReferencePrefix ref, String suffix) {
        if (suffix == null) {
            return toPathName(ref);
        }
        int slength = suffix.length();
        if (slength == 0) {
            return toPathName(ref);
        }
        if (ref instanceof NameReference) {
            int length = ((NameReference) ref).getName().length() + 1 + slength;
            ReferencePrefix rp = ref;
            while (rp instanceof ReferenceSuffix) {
                ReferencePrefix rrp = ((ReferenceSuffix) rp).getReferencePrefix();
                if (rrp == null) {
                    break;
                }
                rp = rrp;
                length += ((NameReference) rp).getName().length() + 1;
            }
            char[] buf = new char[length];
            int i = 0;
            while (rp != ref) {
                String name = ((NameReference) rp).getName();
                int len = name.length();
                name.getChars(0, len, buf, i);
                i += len;
                buf[i++] = '.';
                rp = (ReferencePrefix) rp.getReferenceSuffix();
            }
            String name = ((NameReference) rp).getName();
            int len = name.length();
            name.getChars(0, len, buf, i);
            i += len;
            buf[i++] = '.';
            suffix.getChars(0, slength, buf, i);
            return new String(buf, 0, length);
        }
        return "";
    }

    /*
     * Returns the fully qualified name of the package of a compilation unit.
     *
     * @param cu a compilation unit. @return the canonical name of the unit, or <CODE> "" </CODE> if
     * the unit has the default package.
     */
    public static String getPackageName(CompilationUnit cu) {
        PackageSpecification spec = cu.getPackageSpecification();
        if (spec == null) {
            return "";
        }
        PackageReference pref = spec.getPackageReference();
        if (pref == null || pref.getName() == null) {
            return "";
        }
        return toPathName(pref);
    }

    /**
     * Derives the canonical name for a compilation unit. Combines the name of the package and the
     * name of the primary type declaration. If the primary type declaration is not public, or no
     * type is declared within the compilation unit, it's attempted to keep the old filename
     * instead.
     *
     * @param cu a compilation unit.
     * @return the canonical name of the unit.
     */
    public static String toCanonicalName(CompilationUnit cu) {
        Debug.assertNonnull(cu);
        TypeDeclaration m = cu.getPrimaryTypeDeclaration();
        // TODO Gutzmann - put back in. This is a hack for as long
        // as recoder does not recognize enums as types
        /*
         * if (m == null) { throw new IllegalArgumentException("Compilation unit " + cu.getName() +
         * " has no primary type declaration"); }
         */
        String name;
        if (m == null || (!m.isPublic() && cu.getDataLocation() != null)) {
            // keep original filename, if possible
            String dataLocStr = cu.getDataLocation().toString();
            int lastDot = dataLocStr.lastIndexOf('.');
            int lastSlash = Math.max(dataLocStr.lastIndexOf('/'), dataLocStr.lastIndexOf('\\'));
            String possibleFileName;
            if (lastDot >= lastSlash) {
                possibleFileName = dataLocStr.substring(lastSlash + 1, lastDot);
            } else {
                possibleFileName = dataLocStr.substring(lastSlash + 1);
            }
            // TODO check if filename is correct
            name = possibleFileName;
        } else {
            name = m.getName();
        }
        String pname = getPackageName(cu);
        if (pname.length() == 0) {
            return name;
        } else {
            return dot(pname, name);
        }
    }

    /**
     * Derives the canoncial file name for a compilation unit. Combines the name of the package and
     * the name of the primary type declaration, transforms it into a platform specific file name
     * and appends the ".java" filename suffix.
     *
     * @param cu a compilation unit.
     * @return the canonical file name of the unit.
     */
    public static String toCanonicalFilename(CompilationUnit cu) {
        return dot(makeFilename(toCanonicalName(cu)), "java");
    }

    public static String getFullName(ClassTypeContainer ct, String suffix) {
        StringBuffer buffer = new StringBuffer();
        addName(buffer, ct);
        if (suffix != null && suffix.length() > 0) {
            if (buffer.length() > 0) {
                buffer.append('.');
            }
            buffer.append(suffix);
        }
        return buffer.toString();
    }

    public static String getFullName(ClassTypeContainer ct) {
        StringBuffer buffer = new StringBuffer();
        addName(buffer, ct);
        return buffer.toString();
    }

    public static String getFullName(Field f) {
        StringBuffer buffer = new StringBuffer();
        addName(buffer, f.getContainingClassType());
        buffer.append('.');
        buffer.append(f.getName());
        return buffer.toString();
    }

    private static boolean addName(StringBuffer buffer, ClassTypeContainer c) {
        ClassTypeContainer container = c.getContainer();
        if (container != null) {
            if (container instanceof Method && c instanceof ClassType) {
                int id = System.identityHashCode(container);
                container = container.getContainer();
                if (container != null) {
                    addName(buffer, container);
                    buffer.append('.');
                }
                buffer.append(id);
                buffer.append('.');
            } else if (addName(buffer, container)) {
                buffer.append('.');
            }
        }
        String name = c.getName();
        if (name == null) {
            name = String.valueOf(System.identityHashCode(c));
        }
        if (name.length() > 0) {
            buffer.append(name);
            return true;
        }
        return false;
    }

    /**
     * Checks if the given name is a Java keyword and hence an invalid identifier.
     *
     * @param name the name to check.
     * @return <CODE>true</CODE> if the given name is a keyword, <CODE>false
     * </CODE> otherwise.
     */
    public static boolean isKeyword(String name) {
        return KEYWORDS.contains(name);
    }

}
