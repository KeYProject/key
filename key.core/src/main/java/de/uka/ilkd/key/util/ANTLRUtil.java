/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jspecify.annotations.NullMarked;

/**
 * Utility to reconstruct the original source text from a given ANTLR4 parse tree.
 *
 * It is not 100% accurate, but should be good enough for most use cases.
 *
 * @author Mattias Ulbrich, or rather ChatGPT 5 mini
 */
@NullMarked
public final class ANTLRUtil {
    private ANTLRUtil() {}

    /**
     * Reconstructs the original source text from a given ANTLR4 parse tree.
     */
    public static String reconstructOriginal(ParseTree tree) {
        List<TerminalNode> terminals = new ArrayList<>();
        collectTerminals(tree, terminals);

        StringBuilder sb = new StringBuilder();
        int curLine = -1;
        int curCol = 0;

        for (TerminalNode tn : terminals) {
            Token t = tn.getSymbol();
            if (t == null)
                continue;
            if (t.getType() == Token.EOF)
                continue;

            if (curLine == -1) {
                // use first token to initialize line and column
                curCol = t.getCharPositionInLine();
                curLine = t.getLine();
            }

            int line = t.getLine();
            int col = t.getCharPositionInLine();

            // add newlines to reach the desired line
            while (curLine < line) {
                sb.append('\n');
                curLine++;
                curCol = 0;
            }

            // add spaces to reach the desired column
            int pad = col - curCol;
            if (pad > 0) {
                sb.append(" ".repeat(pad));
                curCol = col;
            }

            String text = t.getText();
            if (text == null)
                text = "";

            sb.append(text);

            // update current position
            int newlines = countOccurrences(text, '\n');
            if (newlines > 0) {
                curLine += newlines;
                int lastNl = text.lastIndexOf('\n');
                curCol = text.length() - lastNl - 1;
            } else {
                curCol += text.length();
            }
        }

        return sb.toString();
    }

    private static void collectTerminals(ParseTree node, List<TerminalNode> out) {
        if (node == null)
            return;
        if (node instanceof TerminalNode) {
            out.add((TerminalNode) node);
            return;
        }
        for (int i = 0; i < node.getChildCount(); i++) {
            collectTerminals(node.getChild(i), out);
        }
    }

    private static int countOccurrences(String s, char c) {
        int cnt = 0;
        for (int i = 0; i < s.length(); i++)
            if (s.charAt(i) == c)
                cnt++;
        return cnt;
    }
}
