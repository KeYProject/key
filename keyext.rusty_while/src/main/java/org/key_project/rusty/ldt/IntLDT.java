package org.key_project.rusty.ldt;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.TermBuilder;

public class IntLDT extends LDT {
    public static final Name NAME = new Name("int");

    public static final Name NUMBERS_NAME = new Name("Z");
    public static final String NEGATIVE_LITERAL_STRING = "neglit";

    private final Function sharp;
    private final Function[] numberSymbol = new Function[10];
    private final Function neglit;
    private final Function numbers;
    private final Function add;
    private final Function neg;
    private final Function sub;
    private final Function mul;
    private final Function div;
    private final Function mod;
    private final Function pow;

    private final Function lessThan;
    private final Function greaterThan;
    private final Function greaterOrEquals;
    private final Function lessOrEquals;

    private final Term one;
    private final Term zero;

    public IntLDT(Services services) {
        super(NAME, services);

// initialise caches for function symbols from integerHeader.key
        sharp = addFunction(services, "#");
        for (int i = 0; i < 10; i++) {
            numberSymbol[i] = addFunction(services, String.valueOf(i));
        }
        neglit = addFunction(services, NEGATIVE_LITERAL_STRING);
        numbers = addFunction(services, NUMBERS_NAME.toString());
        assert sharp.sort() == numbers.argSort(0);
        add = addFunction(services, "add");
        neg = addFunction(services, "neg");
        sub = addFunction(services, "sub");
        mul = addFunction(services, "mul");
        div = addFunction(services, "div");
        mod = addFunction(services, "mod");
        pow = addFunction(services, "pow");

        lessThan = addFunction(services, "lt");
        greaterThan = addFunction(services, "gt");
        greaterOrEquals = addFunction(services, "geq");
        lessOrEquals = addFunction(services, "leq");

        // cache often used constants
        zero = makeDigit(0, services.getTermBuilder());
        one = makeDigit(1, services.getTermBuilder());
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private boolean isNumberLiteral(Operator f) {
        String n = f.name().toString();
        if (n.length() == 1) {
            char c = n.charAt(0);
            return '0' <= c && c <= '9';
        }
        return false;
    }

    private Term makeDigit(int digit, TermBuilder tb) {
        return tb.func(getNumberSymbol(),
                tb.func(getNumberLiteralFor(digit), tb.func(getNumberTerminator())));
    }

    @Override
    public @NonNull Name name() {
        return NAME;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public Function getNumberSymbol() {
        return numbers;
    }

    public Function getNumberTerminator() {
        return sharp;
    }


    public Function getNumberLiteralFor(int number) {
        if (number < 0 || number > 9) {
            throw new IllegalArgumentException(
                    "Number literal symbols range from 0 to 9. Requested was:" + number);
        }

        return numberSymbol[number];
    }

    public Function getNegativeNumberSign() {
        return neglit;
    }

    public Function getAdd() {
        return add;
    }

    public Function getNeg() {
        return neg;
    }

    public Function getSub() {
        return sub;
    }

    public Function getMul() {
        return mul;
    }

    public Function getDiv() {
        return div;
    }

    public Function getMod() {
        return mod;
    }

    public Function getPow() {
        return pow;
    }

    public Function getLessThan() {
        return lessThan;
    }

    public Function getGreaterThan() {
        return greaterThan;
    }

    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }

    public Function getLessOrEquals() {
        return lessOrEquals;
    }

    public Term zero() {
        return zero;
    }

    public Term one() {
        return one;
    }
}
