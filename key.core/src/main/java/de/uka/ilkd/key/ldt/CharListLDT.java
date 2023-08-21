/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import javax.annotation.Nullable;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

import org.key_project.util.ExtList;


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

    private String translateCharTerm(Term t) {
        char charVal = 0;
        int intVal = 0;
        String result = printlastfirst(t.sub(0)).toString();
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


    private StringBuffer printlastfirst(Term t) {
        if (t.op().arity() == 0) {
            return new StringBuffer();
        } else {
            return printlastfirst(t.sub(0)).append(t.op().name().toString());
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
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub,
            TermServices services, ExecutionContext ec) {
        return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        final SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
        final TermBuilder tb = services.getTermBuilder();
        final Term term_empty = tb.func(seqLDT.getSeqEmpty());

        char[] charArray;
        Term result = term_empty;

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
            Term singleton =
                tb.seqSingleton(intLDT.translateLiteral(new CharLiteral(charArray[i]), services));
            result = tb.seqConcat(singleton, result);
        }

        return result;
    }


    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services serv,
            ExecutionContext ec) {
        assert false;
        return null;
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }


    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        final StringBuilder result = new StringBuilder();
        Term term = t;
        while (term.op().arity() != 0) {
            result.append(translateCharTerm(term.sub(0)));
            term = term.sub(1);
        }
        return new StringLiteral("\"" + result + "\"");
    }


    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }

    @Nullable
    @Override
    public Function getFunctionFor(String operationName, Services services) {
        switch (operationName) {
        // This is not very elegant; but seqConcat is actually in the SeqLDT.
        case "add":
            return services.getNamespaces().functions().lookup("seqConcat");
        default:
            return null;
        }
    }
}
