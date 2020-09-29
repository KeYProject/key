package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.List;

/**
 * Simple routine to prettyprint an SMT2 input.
 *
 * This is not specific to KeY at all.
 *
 * However, it is rather pragmatic and I cannot guarantee that it works correctly on all
 * SMTLib2 input.
 *
 * Use the static method {@link #indent(String)} to obtain a nice indented version of
 * your SMTLib2-code.
 *
 * @author Mattias Ulbrich
 */
public class SMTBeautifier {

    // not to be instantiated
    private SMTBeautifier() {
        throw new Error();
    }

    // A kind of "int*" in Java.
    private static class MutableInt {
        private int val;
    }

    // An element is either a single string or a list of elements
    private static class Element {
        private String head;
        private List<Element> children;

        public int length() {
            int result = 0;
            if (head != null) {
                result += head.length();
            }
            if(children != null) {
                for (Element child : children) {
                    result += child.length();
                }
            }
            return result;
        }

        @Override
        public String toString() {
            if (head != null) {
                return head;
            } else {
                return children.toString();
            }
        }

    }

    /**
     * Indent a piece of SMTLib2-code.
     *
     * Each line consists of some initial spaces and then at most 80 characters
     * (not counting spaces again).
     *
     * The code may crash with some {@link IndexOutOfBoundsException} or
     * {@link NullPointerException} if invoked on illegal smt code.
     *
     * @param smtCode the code to indent.
     * @return a string representation equivalent to the input
     */
    public static String indent(String smtCode) {
        return indent(smtCode, 80);
    }

    /**
     * Indent a piece of SMTLib2-code.
     *
     * Each line consists of some initial spaces and then at most lineLength characters
     * (not counting spaces again).
     *
     * The code may crash with some {@link IndexOutOfBoundsException} or
     * {@link NullPointerException} if invoked on illegal smt code.
     *
     * @param smtCode the code to indent.
     * @param lineLength the number of characters per line, > 0
     * @return a string representation equivalent to the input
     */
    public static String indent(String smtCode, int lineLength) {
        MutableInt pos = new MutableInt();
        StringBuilder sb = new StringBuilder();
        while (pos.val < smtCode.length()) {
            Element element = parse(smtCode, pos);
            sb.append(prettyPrint(element, 1, lineLength)).append("\n");
        }
        return sb.toString();
    }

    private static Element parse(String s, MutableInt pos) {
        while (pos.val < s.length()) {
            switch (s.charAt(pos.val)) {
                case ' ':
                case '\t':
                case '\r':
                case '\n':
                    break;

                case '(':
                    return parseParen(s, pos);

                case '|':
                    int start = pos.val;
                    pos.val++;
                    while (s.charAt(pos.val) != '|') {
                        pos.val++;
                    }
                    Element result = new Element();
                    pos.val++;
                    result.head = s.substring(start, pos.val);
                    return result;

                case ';':
                    start = pos.val;
                    pos.val++;
                    while (pos.val < s.length() && s.charAt(pos.val) != '\n') {
                        pos.val++;
                    }
                    result = new Element();
                    pos.val++;
                    result.head = s.substring(start, Math.min(s.length() - 1, pos.val));
                    return result;

                default:
                    start = pos.val;
                    pos.val++;
                    while (pos.val < s.length() && " \t\n();|".indexOf(s.charAt(pos.val)) == -1) {
                        pos.val++;
                    }
                    result = new Element();
                    result.head = s.substring(start, pos.val);
                    return result;
            }
            pos.val ++;
        }
        return new Element();
    }

    private static Element parseParen(String s, MutableInt pos) {
        assert s.charAt(pos.val) == '(';
        Element result = new Element();
        result.children = new ArrayList<>();
        pos.val ++;
        while (pos.val < s.length() && s.charAt(pos.val) != ')') {
            result.children.add(parse(s, pos));
            while(pos.val < s.length() && Character.isSpaceChar(s.charAt(pos.val))) {
                pos.val ++;
            }
        }
        pos.val++;
        return result;
    }

    private static CharSequence prettyPrint(Element element, int indent, int lineLength) {
        if (element.head == null) {
            StringBuilder sb = new StringBuilder("(");
            boolean breakLines = (element.length() < lineLength);
            boolean first = true;
            for (Element child : element.children) {
                if (first) {
                    first = false;
                } else {
                    if(breakLines) {
                        sb.append(" ");
                    } else {
                        sb.append("\n");
                        for (int i = 0; i < indent; i++) {
                            sb.append("  ");
                        }
                    }
                }
                sb.append(prettyPrint(child, indent + 1, lineLength));
            }
            sb.append(")");
            return sb;

        } else {
            return element.head;
        }

    }
}
