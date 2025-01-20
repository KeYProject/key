/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.List;

import recoder.ProgramFactory;
import recoder.java.DocComment;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

public class CommentKit {

    private CommentKit() {
        // do not instantiate
    }

    /**
     * Factory method creating an empty or faked comment conforming to JavaDoc conventions for the
     * given method declaration.
     *
     * @param method a non- <CODE>null</CODE> method declaration.
     * @param dummy flag to indicate whether a fake comment text should be inserted.
     * @return a brand-new doc comment.
     */
    public static DocComment createDoc(MethodDeclaration method, boolean dummy) {

        Debug.assertNonnull(method);
        StringBuilder text = new StringBuilder("/**\n");
        if (dummy) {
            text.append("  ");
            text.append(guessDocumentation(method.getName(), true));
            text.append("\n");
        }
        int c = method.getParameterDeclarationCount();
        for (int i = 0; i < c; i += 1) {
            ParameterDeclaration param = method.getParameterDeclarationAt(i);
            text.append("  @param ").append(param.getVariables().get(0).getName()).append(' ');
            if (dummy) {
                text.append(guessDocumentation(param.getTypeReference(), false));
            }
            text.append('\n');
        }
        TypeReference ret = method.getTypeReference();
        if (ret != null && !"void".equals(ret.getName())) {
            text.append("  @return ");
            if (dummy) {
                text.append(guessDocumentation(ret, true));
            }
            text.append('\n');
        }
        Throws th = method.getThrown();
        if (th != null) {
            List<TypeReference> excepts = th.getExceptions();
            for (TypeReference tr : excepts) {
                text.append("  @exception ").append(tr.getName());
                if (dummy) {
                    text.append(" occasionally thrown.\n");
                }
            }
        }
        text.append("*/");
        return method.getFactory().createDocComment(text.toString());
    }

    /**
     * Factory method creating an empty or faked comment conforming to JavaDoc conventions for the
     * given field declaration.
     *
     * @param field a non- <CODE>null</CODE> field declaration.
     * @param dummy flag to indicate whether a fake comment text should be inserted.
     * @return a brand-new doc comment.
     */
    public static DocComment createDoc(FieldDeclaration field, boolean dummy) {
        Debug.assertNonnull(field);
        ProgramFactory factory = field.getFactory();
        if (dummy) {
            String name = field.getVariables().get(0).getName();
            return factory.createDocComment("/**\n  " + guessDocumentation(name, true) + "\n*/");
        } else {
            return factory.createDocComment("/**\n  \n*/");
        }
    }

    /**
     * Factory method creating an empty or faked comment conforming to JavaDoc conventions for the
     * given field declaration. This variant creates an empty serial tag when the enclosing type is
     * a class implementing <CODE>
     * java.io.Serializable</CODE>.
     *
     * @param si the source info service.
     * @param ni the name info service.
     * @param field a non- <CODE>null</CODE> field declaration.
     * @param dummy flag to indicate whether a fake comment text should be inserted.
     * @return a brand-new doc comment.
     */
    public static DocComment createDoc(SourceInfo si, NameInfo ni, FieldDeclaration field,
            boolean dummy) {
        Debug.assertNonnull(field);
        boolean isSerial;
        TypeDeclaration td = MiscKit.getParentTypeDeclaration(field);
        if (td instanceof ClassDeclaration) {
            isSerial = si.isSubtype(td, ni.getJavaIoSerializable());
        } else {
            isSerial = false;
        }
        ProgramFactory factory = field.getFactory();
        if (dummy) {
            String name = field.getVariables().get(0).getName();
            return factory.createDocComment("/**\n  " + guessDocumentation(name, true)
                + (isSerial ? "\n  @serial" : "") + "\n*/");
        } else {
            return factory.createDocComment("/**\n  " + (isSerial ? "\n  @serial" : "") + "n*/");
        }
    }

    /**
     * Factory method creating an empty or faked comment conforming to JavaDoc conventions for the
     * given type declaration.
     *
     * @param type a non- <CODE>null</CODE> type declaration.
     * @param dummy flag to indicate whether a fake comment text should be inserted.
     * @return a brand-new doc comment.
     */
    public static DocComment createDoc(TypeDeclaration type, boolean dummy) {
        Debug.assertNonnull(type);
        ProgramFactory factory = type.getFactory();
        if (dummy) {
            String name = type.getName();
            return factory.createDocComment(
                "/**\n  " + guessDocumentation(name, true) + "\n  @author " + "\n*/");
        } else {
            return factory.createDocComment("/**\n  \n*/");
        }
    }

    /**
     * Guesses a documentation for the given type (reference). The generated documentation perfectly
     * describes the type, given that it is perfectly self-explanatory ;)
     *
     * @param tr a type reference.
     * @param returned flag indicating if the documentation should describe a method return value.
     * @return the description string.
     */
    static String guessDocumentation(TypeReference tr, boolean returned) {
        String tn = tr.getName();
        if (tr.getDimensions() == 0) {
            if (tn.equals("int") || tn.equals("boolean") || tn.equals("short") || tn.equals("long")
                    || tn.equals("byte") || tn.equals("char") || tn.equals("float")
                    || tn.equals("double")) {
                tn += " value";
            }
        }
        String ty = guessDocumentation(tn, false);
        switch (tr.getDimensions()) {
        case 0:
            if (returned) {
                return "the " + ty;
            }
            if ("aeiouAEIOU".indexOf(ty.charAt(0)) >= 0) {
                return "an " + ty;
            } else {
                return "a " + ty;
            }
        case 1:
            return (returned ? "the" : "an") + " array of " + ty;
        case 2:
            return (returned ? "the" : "a") + " matrix of " + ty;
        default:
            return (returned ? "the" : "a") + " multi-dimensional array of " + ty;
        }
    }

    /**
     * Derives a documentation from a given name. The method assumes that the Sun conventions are
     * met and separates the words: <TT>
     * guessDocumentation("HelloWorld", false) == "hello world."</TT>
     *
     * @param name a string used as an identifier.
     * @param capital flag indicating if the first word of the derived documentation should start
     *        with a capital letter.
     * @return the description string.
     */
    static String guessDocumentation(String name, boolean capital) {
        // to do: enable '_' as separator, check if parts are completely
        // capitalized (e.g. for constants)
        int len = name.length();
        StringBuilder res = new StringBuilder(len + 6);
        for (int i = 0; i < len; i += 1) {
            char ch = name.charAt(i);
            if (Character.isUpperCase(ch)) {
                if (i < len - 1 && Character.isUpperCase(name.charAt(i + 1))) {
                    if (i > 0 && !Character.isUpperCase(name.charAt(i - 1))) {
                        res.append(' ');
                    }
                    res.append(ch);
                } else {
                    if (i > 0) {
                        res.append(' ');
                    }
                    res.append(Character.toLowerCase(ch));
                }
            } else {
                res.append(ch);
            }
        }
        if (capital) {
            res.setCharAt(0, Character.toUpperCase(res.charAt(0)));
        }
        res.append('.');
        return res.toString();
    }
}
