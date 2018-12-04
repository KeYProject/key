package de.uka.ilkd.key.logic.label;

import java.util.HashSet;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.StringTokenizer;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;

public class OriginTermLabelFactory implements TermLabelFactory<OriginTermLabel> {

    @Override
    public OriginTermLabel parseInstance(List<String> arguments, TermServices services) throws TermLabelException {
        if (arguments.size() != OriginTermLabel.CHILD_COUNT) {
            throw new TermLabelException(
                    "OriginTermLabel has "
                            + arguments.size()
                            + " children, but should have " + OriginTermLabel.CHILD_COUNT);
        }

        Origin origin = parseOrigin(arguments.get(0));
        Set<Origin> subtermOrigins = parseSubtermOrigins(arguments.get(1));

        return new OriginTermLabel(origin, subtermOrigins);
    }

    private Set<Origin> parseSubtermOrigins(String str) throws TermLabelException {
        if (!str.startsWith("[") || !str.endsWith("]")) {
            throw new TermLabelException("Malformed set of origins: \"" + str + "\"\n"
                    + "(Should be a comma-separated set of of origins, delimited by \"[\" and \"]\"");
        }

        Set<Origin> result = new HashSet<>();

        for (String s : str.substring(1, str.length() - 1).split("\\s*,\\s*")) {
            if (s.isEmpty()) {
                break;
            }

            result.add(parseOrigin(s));
        }

        return result;
    }

    private Origin parseOrigin(String str) throws TermLabelException {
        try {
            StringTokenizer tokenizer = new StringTokenizer(str, " ");

            SpecType specType = parseSpecType(tokenizer.nextToken());

            String token = tokenizer.nextToken();

            if (token.equals("(implicit)")) {
                matchEnd(tokenizer, str);

                return new Origin(specType, null, -1);
            } else {
                matchChar(token, str, "@");

                String filename = tokenizer.nextToken();
                matchChar(tokenizer.nextToken(), str, "@");
                matchId(tokenizer.nextToken(), str, "line");
                int line = Integer.parseInt(tokenizer.nextToken());
                matchEnd(tokenizer, str);

                return new Origin(specType, filename, line);
            }
        } catch (NoSuchElementException | IllegalArgumentException e) {
            throw new TermLabelException("Malformed origin string: \"" + str + "\"\n"
                    + "(Well-formed origins look like this: \"spec_type @ filename @ line xx\")\n"
                    + "(                      or like this: \"spec_type (implicit)\")\n");
        }
    }

    private SpecType parseSpecType(String str) {
        if (str.toLowerCase().equals(SpecType.NONE.toString())) {
            str = "none";
        }

        return SpecType.valueOf(str.toUpperCase());
    }

    private String matchId(String actual, String line, String expected)
            throws TermLabelException {
        if (!expected.equals(actual)) {
            throw new TermLabelException("Unexpected token \"" + actual + "\", "
                    + "expected: \"" + expected + "\""
                    + "\nin line \"" + line + "\"");
        }

        return expected;
    }

    private char matchChar(String actual, String line, String expected)
            throws TermLabelException {
        if (actual.length() != 1 || !expected.contains(actual)) {
            throw new TermLabelException("Unexpected token \"" + actual + "\", "
                    + "expected any of: " + expected
                    + "\nin line \"" + line + "\"");
        }

        return actual.charAt(0);
    }

    private void matchEnd(StringTokenizer tokenizer, String line) throws TermLabelException {
        if (tokenizer.hasMoreTokens()) {
            throw new TermLabelException("Unexpected token \'" + tokenizer.nextToken() + "\', "
                    + "expected: \'\"\'"
                    + "\nin line \"" + line + "\"");
        }
    }
}
