/*
 * KEY
 */

/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class models s-expressions to be used for the SMT translation.
 *
 * Every s-expression has got a {@link #name} and a (potentially empty) list of
 * {@link #children}.
 *
 * They can be printed out, non-simple names are escaped for SMT.
 *
 * @author Mattias Ulbrich
 *
 */
public class SExpr implements Writable {

    public enum Type {
        /** to indicate that this expression holds a value of type Int */
        INT,
        /** to indicate that this expression holds a value of type Bool */
        BOOL,
        /** to indicate that this expression holds a value of type U */
        UNIVERSE,
        /** to indicate that this expression has some unknown type */
        NONE,
        /** to indicate that this element needs no escaping despite its name */
        VERBATIM
    }

    private static final Pattern EXTRACHAR_PATTERN =
            Pattern.compile("[^-A-Za-z0-9+/*=%?!.$_~&^<>@]");

    private final String name;
    private final Type type;

    private List<SExpr> children;

    public SExpr(String name, Type type) {
        this.name = name;
        this.type = type;
        this.children = Collections.emptyList();
    }

    public SExpr(String name) {
        this(name, Type.NONE);
    }

    public SExpr(String name, Type type, List<SExpr> children) {
        this.name = name;
        this.type = type;
        this.children = children;
    }

    public SExpr(String name, List<SExpr> children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, String... children) {
        this.name = name;
        this.type = type;
        this.children = new ArrayList<>();
        for (String string : children) {
            this.children.add(new SExpr(string));
        }
    }

    public SExpr(String name, String... children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, SExpr... children) {
        this(name, type, Arrays.asList(children));
    }

    public SExpr(String name, SExpr... children) {
        this(name, Type.NONE, children);
    }

    public SExpr(SExpr... children) {
        this("", Type.NONE, children);
    }

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

    public List<SExpr> getChildren() {
        return Collections.unmodifiableList(children);
    }

    private String getEscapedName() {
        if (name.length() > 0 && name.charAt(0) == '|' && name.charAt(name.length() - 1) == '|') {
            return name; //already escaped
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

    @Override
    public void appendTo(StringBuilder sb) {
        boolean noSpace = name.isEmpty();
        if(children.size() > 0 || noSpace) {
            sb.append("(").append(getEscapedName());
            for (SExpr child : children) {
                if(!noSpace) {
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

    public Type getType() {
        return type;
    }

    public SExpr map(Function<SExpr, SExpr> mapFunction) {
        return new SExpr(name, children.stream().map(mapFunction).collect(Collectors.toList()));
    }


}
