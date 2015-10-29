package org.key_project.jmlediting.core.profile.syntax;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * An {@link AbstractKeyword} does some default implementation for an
 * {@link IKeyword}.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractKeyword implements IKeyword {

    /**
     * A set of all supported keywords.
     */
    private final Set<String> keywords;

    /**
     * Creates a new {@link AbstractKeyword}. The list of supported keywords is
     * converted to a set, but for easier code the varargs are used in the
     * constructor.
     *
     * @param keyword
     *            the first keyword
     * @param keywords
     *            all other supported keywords
     */
    public AbstractKeyword(final String keyword, final String... keywords) {
        super();
        switch (keywords.length) {
        case 0:
            // Do some performance optimizations for the regular case that we
            // have
            // only one keyword
            this.keywords = Collections.singleton(keyword);
            break;
        default:
            final HashSet<String> k = new HashSet<String>(
                    Arrays.asList(keywords));
            k.add(keyword);
            this.keywords = Collections.unmodifiableSet(k);
        }
        // Validate keywords
        for (final String k : this.keywords) {
            validateKeyword(k);
        }
    }

    /**
     * Creates a new {@link AbstractKeyword}. The set of supported keywords is
     * not allowed to be empty.
     *
     * @param keywords
     *            all supported keywords
     */
    public AbstractKeyword(final Set<String> keywords) {
        if (keywords.isEmpty()) {
            throw new IllegalArgumentException(
                    "Need to provide at least one keyword");
        }
        // Validate keywords
        for (final String keyword : keywords) {
            validateKeyword(keyword);
        }
        this.keywords = Collections.unmodifiableSet(keywords);
    }

    /**
     * Ensures that the keyword does not contains white spaces. Otherwise it
     * throws an exception.
     *
     * @param keyword
     *            the keyword to validate
     */
    private static void validateKeyword(final String keyword) {
        for (final char c : keyword.toCharArray()) {
            if (Character.isWhitespace(c)) {
                throw new IllegalArgumentException(
                        "The keyword is not allowed to contain whitespaces.");
            }
        }
    }

    @Override
    public Set<String> getKeywords() {
        return keywords;
    }

    @Override
    public IKeywordAutoProposer createAutoProposer() {
        return null;
    }

    /**
     * Default Implementation, returns null so there is no Validator. Subclasses
     * have to override if there is a Validator.
     *
     * @return null
     */
    @Override
    public IKeywordValidator getKeywordValidator() {
        return null;
    }

}
