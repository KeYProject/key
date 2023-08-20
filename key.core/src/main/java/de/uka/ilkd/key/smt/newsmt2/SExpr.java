/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.UnaryOperator;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * This class models s-expressions to be used for the SMT translation.
 * <p>
 * Every s-expression has got a {@link #name} and a (potentially empty) list of {@link #children}.
 * <p>
 * They can be printed out, non-simple names are escaped for SMT.
 *
 * @author Mattias Ulbrich
 */
public class SExpr implements Writable {

    /**
     * An enumeration of the types that an {@link SExpr} can assume.
     */
    public static class Type {

        /** to indicate that this expression holds a value of type U */
        public static final Type UNIVERSE = new Type("Universe", null, null);
        /** to indicate that this expression has other or unknown type */
        public static final Type NONE = new Type("None", null, null);
        /** to indicate that this element needs no escaping despite its name */
        public static final Type VERBATIM = new Type("Verbatim", null, null);

        /** to indicate that an expression holds a value of type Bool */
        public static final Type BOOL = new Type("Bool", "b2u", "u2b");

        public final String name;
        public final String injection;
        public final String projection;

        public Type(String name, String injection, String projection) {
            this.name = name;
            this.injection = injection;
            this.projection = projection;
        }

        @Override
        public String toString() {
            return name;
        }
    }

    /** The regular expression used to check if |...| escapes are needed. */
    private static final Pattern EXTRACHAR_PATTERN =
        Pattern.compile("[^-#A-Za-z0-9+/*=%?!.$_~&^<>@]");

    /** The string name of the atom used in this sexpr. */
    private final String name;

    /** The type of this sexpr. Not null */
    private final Type type;

    /** The collection of the direct child s-expr of this object. Not null */
    private final List<SExpr> children;

    /**
     * Create a new s-expr without children, but with a given type.
     *
     * @param name the non-null name of the atom
     * @param type the non-null type to use
     */
    public SExpr(String name, Type type) {
        this.name = Objects.requireNonNull(name);
        this.type = Objects.requireNonNull(type);
        this.children = Collections.emptyList();
    }

    /**
     * Create a new s-expr without children of type {@link Type#NONE}.
     *
     * @param name the non-null name of the atom
     */
    public SExpr(String name) {
        this(name, Type.NONE);
    }

    /**
     * Create a new s-expr with children and a given type.
     *
     * @param name the non-null name of the atom
     * @param type the non-null type to use
     * @param children the list of children to use. Should not be modified elsewhere
     */
    public SExpr(String name, Type type, List<SExpr> children) {
        this.name = name;
        this.type = type;
        this.children = children;
    }

    /**
     * Create a new s-expr with children and type {@link Type#NONE}.
     *
     * @param name the non-null name of the atom
     * @param children the list of children to use. Should not be modified elsewhere
     */
    public SExpr(String name, List<SExpr> children) {
        this(name, Type.NONE, children);
    }

    /**
     * Create a new s-expr with children and a given type.
     *
     * The array of String children is mapped to a list of {@link SExpr}s.
     *
     * @param name the non-null name of the atom
     * @param type the non-null type to use
     * @param children the list of children to use.
     */
    public SExpr(String name, Type type, String... children) {
        this(name, type, asSExprs(children));
    }

    private static List<SExpr> asSExprs(String[] children) {
        List<SExpr> result = new ArrayList<>();
        for (String child : children) {
            result.add(new SExpr(child));
        }
        return result;
    }

    /**
     * Create a new s-expr with children and type {@link Type#NONE}.
     *
     * The array of String children is mapped to a list of {@link SExpr}s.
     *
     * @param name the non-null name of the atom
     * @param children the list of children to use.
     */
    public SExpr(String name, String... children) {
        this(name, Type.NONE, children);
    }

    /**
     * Create a new s-expr with children and a given type.
     *
     * @param name the non-null name of the atom
     * @param type the non-null type to use
     * @param children the list of children to use.
     */
    public SExpr(String name, Type type, SExpr... children) {
        this(name, type, Arrays.asList(children));
    }

    /**
     * Create a new s-expr with children and type {@link Type#NONE}.
     *
     * @param name the non-null name of the atom
     * @param children the list of children to use.
     */
    public SExpr(String name, SExpr... children) {
        this(name, Type.NONE, children);
    }

    /**
     * Create a new s-expr without atomic name (set to "") with children and type {@link Type#NONE}.
     *
     * @param children the list of children to use.
     */
    public SExpr(SExpr... children) {
        this("", Type.NONE, children);
    }

    /**
     * Create a new s-expr without atomic name (set to "") with children and type {@link Type#NONE}.
     *
     * @param children the list of children to use. Should not be modified elsewhere.
     */
    public SExpr(List<SExpr> children) {
        this("", Type.NONE, children);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        appendTo(sb);
        return sb.toString();
    }

    public String getName() {
        return name;
    }

    public Type getType() {
        return type;
    }

    public List<SExpr> getChildren() {
        return Collections.unmodifiableList(children);
    }

    /**
     * The atomic name may be an arbitrary string without '|'.
     *
     * If certain characters occur in the string, it needs to be escaped between |...| to make it a
     * valid SMTLIB2 identifier.
     *
     * Items of type {@link Type#VERBATIM} are not escaped since they are deliberately indicated as
     * special.
     *
     * @return the non-null SMTLIB2-valid name of this object, potentially escaped.
     */
    private String getEscapedName() {
        if (name.length() > 0 && name.charAt(0) == '|' && name.charAt(name.length() - 1) == '|') {
            return name; // already escaped
        }
        if (type == Type.VERBATIM) {
            return name;
        }
        if (EXTRACHAR_PATTERN.matcher(name).find()) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

    /**
     * Append the SMTLIB2-representation of this object to the given string builder.
     *
     * @param sb a non-null string builder to write to.
     */
    @Override
    public void appendTo(StringBuilder sb) {
        boolean noSpace = name.isEmpty();
        if (!children.isEmpty() || noSpace) {
            sb.append("(").append(getEscapedName());
            for (SExpr child : children) {
                if (!noSpace) {
                    sb.append(" ");
                } else {
                    noSpace = false;
                }
                child.appendTo(sb);
            }
            sb.append(")");
        } else {
            sb.append(getEscapedName());
        }
    }

    /**
     * Create a new {@link SExpr} by applying a function to all children of this object.
     *
     * The atomic name is not modified, nor is the function applied in depth.
     *
     * @param mapFunction a non-null function to be applied to the children.
     *
     * @return a new SEXpr with the same name and type and with the mapFunction applied to all
     *         children.
     */
    public SExpr map(UnaryOperator<SExpr> mapFunction) {
        return new SExpr(name, type,
            children.stream().map(mapFunction).collect(Collectors.toList()));
    }

}
