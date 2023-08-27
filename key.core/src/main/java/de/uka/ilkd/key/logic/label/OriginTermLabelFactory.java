/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.nio.file.Paths;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.StringTokenizer;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.OriginTermLabel.FileOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.NodeOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;

/**
 * Factory for {@link OriginTermLabel}s.
 *
 * @author lanzinger
 */
public class OriginTermLabelFactory implements TermLabelFactory<OriginTermLabel> {

    @Override
    public OriginTermLabel parseInstance(List<String> arguments, TermServices services)
            throws TermLabelException {
        if (arguments.size() != OriginTermLabel.CHILD_COUNT) {
            throw new TermLabelException("OriginTermLabel has " + arguments.size()
                + " children, but should have " + OriginTermLabel.CHILD_COUNT);
        }

        Origin origin = parseOrigin(arguments.get(0));
        Set<Origin> subtermOrigins = parseSubtermOrigins(arguments.get(1));

        return new OriginTermLabel(origin, subtermOrigins);
    }

    /**
     * Parses a set of origins.
     *
     * @param str the string to parse.
     * @return the parsed set of origins.
     * @throws TermLabelException if a parsing error occurs.
     */
    private Set<Origin> parseSubtermOrigins(String str) throws TermLabelException {
        if (!str.startsWith("[") || !str.endsWith("]")) {
            throw new TermLabelException("Malformed set of origins: \"" + str + "\"\n"
                + "(Should be a comma-separated set of of origins, "
                + "delimited by \"[\" and \"]\"");
        }

        Set<Origin> result = new LinkedHashSet<>();

        for (String s : str.substring(1, str.length() - 1).split("\\s*,\\s*")) {
            if (s.isEmpty()) {
                break;
            }

            result.add(parseOrigin(s));
        }

        return result;
    }

    /**
     * Parses an origin.
     *
     * @param str the string to parse.
     * @return the parsed origin.
     * @throws TermLabelException if a parsing error occurs.
     */
    private Origin parseOrigin(String str) throws TermLabelException {
        try {
            StringTokenizer tokenizer = new StringTokenizer(str, " ");

            SpecType specType = parseSpecType(tokenizer.nextToken());

            String token = tokenizer.nextToken();

            if (token.equals("(implicit)")) {
                matchEnd(tokenizer, str);

                return new Origin(specType);
            } else {
                matchChar(token, str, "@");

                token = tokenizer.nextToken();

                if (token.equals("file")) {
                    String filename = tokenizer.nextToken();

                    matchChar(tokenizer.nextToken(), str, "@");
                    matchId(tokenizer.nextToken(), str, "line");
                    int line = Integer.parseInt(tokenizer.nextToken());
                    matchEnd(tokenizer, str);

                    return new FileOrigin(specType, Paths.get(filename).toUri(), line);
                } else if (token.equals("node")) {
                    int number = Integer.parseInt(tokenizer.nextToken());

                    String ruleName = tokenizer.nextToken();

                    if (!ruleName.startsWith("(") || !ruleName.endsWith(")")) {
                        throw new IllegalArgumentException();
                    }

                    ruleName = ruleName.substring(1, ruleName.length() - 1);

                    matchEnd(tokenizer, str);

                    return new NodeOrigin(specType, ruleName, number);
                } else {
                    throw new IllegalArgumentException();
                }
            }
        } catch (NoSuchElementException | IllegalArgumentException e) {
            throw new TermLabelException("Malformed origin string: \"" + str + "\"\n"
                + "(Well-formed origins have one of the following formats: \""
                + "spec_type @ file <file name> @ line <line number>\")\n"
                + "spec_type @ node <node number> (<rule name>)\")\n"
                + "spec_type (implicit)\")\n");
        }
    }

    /**
     * Parses a spec type.
     *
     * @param str the string to parse.
     * @return the parsed spec type.
     */
    private SpecType parseSpecType(String str) {
        if (str.toLowerCase().equals(SpecType.NONE.toString())) {
            str = "none";
        }

        return SpecType.valueOf(str.toUpperCase());
    }

    /**
     * Throws an exception if {@code !expected.equals(actual)}
     *
     * @param actual a token.
     * @param line the current line.
     * @param expected the expected token.
     * @return the token.
     * @throws TermLabelException if {@code !expected.equals(actual)}
     */
    private String matchId(String actual, String line, String expected) throws TermLabelException {
        if (!expected.equals(actual)) {
            throw new TermLabelException("Unexpected token \"" + actual + "\", " + "expected: \""
                + expected + "\"" + "\nin line \"" + line + "\"");
        }

        return expected;
    }

    /**
     * Throws an exception if the token is not a single character, or it does not occur in
     * {@code expected.}
     *
     * @param actual a token.
     * @param line the current line.
     * @param expected a string containing the expected characters.
     * @return the token as a single character.
     * @throws TermLabelException if the token is not a single character, or it does not occur in
     *         {@code expected.}
     */
    private char matchChar(String actual, String line, String expected) throws TermLabelException {
        if (actual.length() != 1 || !expected.contains(actual)) {
            throw new TermLabelException("Unexpected token \"" + actual + "\", "
                + "expected any of: " + expected + "\nin line \"" + line + "\"");
        }

        return actual.charAt(0);
    }

    /**
     * Throws an exception if the tokenizer has more tokens.
     *
     * @param tokenizer the tokenizer.
     * @param line the current line.
     * @throws TermLabelException if the tokenizer has more tokens.
     */
    private void matchEnd(StringTokenizer tokenizer, String line) throws TermLabelException {
        if (tokenizer.hasMoreTokens()) {
            throw new TermLabelException("Unexpected token '" + tokenizer.nextToken() + "', "
                + "expected: '\"'" + "\nin line \"" + line + "\"");
        }
    }
}
