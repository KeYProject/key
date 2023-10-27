/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Term;


public final class CharListNotation extends Notation {
    public CharListNotation() {
        super(130);
    }

    @Override
    public void print(Term t, LogicPrinter sp) {
        if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
            sp.printTerm(t);
        } else {
            try {
                sp.printConstant(translateTerm(t));
            } catch (IllegalArgumentException exc) {
                sp.printFunctionTerm(t);
            }
        }
    }

    private StringBuffer printlastfirst(Term t) {
        if (t.op().arity() == 0) {
            return new StringBuffer();
        } else {
            return printlastfirst(t.sub(0)).append(t.op().name().toString());
        }
    }

    private String translateCharTerm(Term t) {
        char charVal = 0;
        int intVal = 0;
        if (t.op().arity() == 0) {
            throw new IllegalArgumentException("Term is not a value!");
        }
        String result = printlastfirst(t.sub(0)).toString();
        try {
            intVal = Integer.parseInt(result);
            charVal = (char) intVal;
            if (intVal - charVal != 0) {
                throw new NumberFormatException(); // overflow!
            }

        } catch (NumberFormatException ex) {
            throw new IllegalArgumentException(result + " is not of type char");
        }
        return String.valueOf(charVal);
    }

    /**
     * translates a term that represents a string literal into a string that is enclosed by
     * quotation marks
     */
    private String translateTerm(Term t) {
        final StringBuilder result = new StringBuilder();
        Term term = t;
        while (!term.op().name().toString().equals("clEmpty")) {
            if (!term.op().name().toString().equals("clCons")) {
                throw new IllegalArgumentException("Term does not represent a String Literal!");
            }
            result.append(translateCharTerm(term.sub(0)));
            term = term.sub(1);
        }
        return "\"" + result + "\"";
    }
}
