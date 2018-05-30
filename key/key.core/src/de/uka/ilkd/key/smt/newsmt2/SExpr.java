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
import java.util.regex.Pattern;

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
public class SExpr {

    public enum Type {
        INT, BOOL, UNIVERSE, PATTERN, NONE
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
        this.children = new ArrayList<SExpr>();
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

    public static SExpr patternSExpr(SExpr e, SExpr... patterns) {
        return new SExpr("! " + e.toString() + " :pattern ", Type.PATTERN, new SExpr(patterns));
    }

    public static SExpr sortExpr(Sort sort) {
        return new SExpr(ModularSMTLib2Translator.SORT_PREFIX + sort.toString());
    }

    public static SExpr castExpr(SExpr sortExp, SExpr exp) {
        return new SExpr("cast", Type.UNIVERSE, exp, sortExp);
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        appendTo(sb);
        return sb.toString();
    }

    public String getEscapedName() {
        if (EXTRACHAR_PATTERN.matcher(name).find() && type != Type.PATTERN) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

    public void appendTo(StringBuffer sb) {
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
}
