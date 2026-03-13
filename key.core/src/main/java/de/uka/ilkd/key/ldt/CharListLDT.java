/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;


public final class CharListLDT extends LDT {

    public static final Name NAME = new Name("CharList");

    public static final Name STRINGPOOL_NAME = new Name("strPool");
    public static final Name STRINGCONTENT_NAME = new Name("strContent");


    // Warning: Some names of char list functions are hardcoded into
    // LexPathOrdering and into CharListNotation!

    // functions
    private final Function clIndexOfChar;
    private final Function clIndexOfCl;
    private final Function clLastIndexOfChar;
    private final Function clLastIndexOfCl;
    private final Function clReplace;
    private final Function clTranslateInt;
    private final Function clRemoveZeros;
    private final Function clHashCode;

    // predicates
    private final Function clStartsWith;
    private final Function clEndsWith;
    private final Function clContains;



    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public CharListLDT(TermServices services) {
        super(NAME, services.getNamespaces().sorts().lookup(SeqLDT.NAME), services);
        clIndexOfChar = addFunction(services, "clIndexOfChar");
        clIndexOfCl = addFunction(services, "clIndexOfCl");
        clLastIndexOfChar = addFunction(services, "clLastIndexOfChar");
        clLastIndexOfCl = addFunction(services, "clLastIndexOfCl");
        clReplace = addFunction(services, "clReplace");
        clTranslateInt = addFunction(services, "clTranslateInt");
        clRemoveZeros = addFunction(services, "clRemoveZeros");
        clHashCode = addFunction(services, "clHashCode");

        clStartsWith = addFunction(services, "clStartsWith");
        clEndsWith = addFunction(services, "clEndsWith");
        clContains = addFunction(services, "clContains");
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private String translateCharTerm(JTerm t) {
        char charVal;
        int intVal;
        String result = printLastFirst(t.sub(0)).toString();
        try {
            intVal = Integer.parseInt(result);
            charVal = (char) intVal;
            if (intVal - charVal != 0) {
                throw new NumberFormatException(); // overflow!
            }

        } catch (NumberFormatException ex) {
            throw new ConvertException(result + " is not of type char");
        }
        return String.valueOf(charVal);
    }


    private StringBuffer printLastFirst(JTerm t) {
        if (t.op().arity() == 0) {
            return new StringBuffer();
        } else {
            return printLastFirst(t.sub(0)).append(t.op().name());
        }
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------


    public Function getClIndexOfChar() {
        return clIndexOfChar;
    }


    public Function getClIndexOfCl() {
        return clIndexOfCl;
    }


    public Function getClLastIndexOfChar() {
        return clLastIndexOfChar;
    }


    public Function getClLastIndexOfCl() {
        return clLastIndexOfCl;
    }


    public Function getClReplace() {
        return clReplace;
    }


    public Function getClTranslateInt() {
        return clTranslateInt;
    }


    public Function getClRemoveZeros() {
        return clRemoveZeros;
    }


    public Function getClHashCode() {
        return clHashCode;
    }


    public Function getClStartsWith() {
        return clStartsWith;
    }


    public Function getClEndsWith() {
        return clEndsWith;
    }


    public Function getClContains() {
        return clContains;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm[] subs,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(Operator op, JTerm sub,
            TermServices services, ExecutionContext ec) {
        return false;
    }


    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        final SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
        final TermBuilder tb = services.getTermBuilder();
        final JTerm term_empty = tb.func(seqLDT.getSeqEmpty());

        char[] charArray;
        JTerm result = term_empty;

        if (lit instanceof StringLiteral) {
            charArray = ((StringLiteral) lit).getValue().toCharArray();
        } else {
            return null;
        }

        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
        if (intLDT == null) {
            throw new IllegalArgumentException(
                "IntegerLDT is needed for StringLiteral translation");
        }

        for (int i = charArray.length - 2; i >= 1; i--) {
            JTerm singleton =
                tb.seqSingleton(intLDT.translateLiteral(new CharLiteral(charArray[i]), services));
            result = tb.seqConcat(singleton, result);
        }

        return result;
    }


    @Override
    public Function getFunctionFor(Operator op, Services serv,
            ExecutionContext ec) {
        assert false;
        return null;
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }


    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        final StringBuilder result = new StringBuilder();
        JTerm term = t;
        while (term.op().arity() != 0) {
            result.append(translateCharTerm(term.sub(0)));
            term = term.sub(1);
        }
        return new StringLiteral("\"" + result + "\"");
    }


    @Override
    public Type getType(JTerm t) {
        assert false;
        return null;
    }

    @Override
    public @Nullable Function getFunctionFor(String operationName, Services services) {
        // This is not very elegant; but seqConcat is actually in the SeqLDT.
        if (operationName.equals("add")) {
            return services.getNamespaces().functions().lookup("seqConcat");
        }
        return null;
    }
}
