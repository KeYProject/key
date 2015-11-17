package org.key_project.jmlediting.core.profile.syntax;

import java.util.Set;

/**
 * The {@link IKeyword} specifies an JML keyword.
 *
 * @author Moritz Lichter
 *
 */
public interface IKeyword {

    /**
     * Returns the keywords. The set is not allowed to be modified and is
     * guaranteed to contains at least one value. It is not allowed to have
     * multiple {@link IKeyword} objects containing the same keyword.
     *
     * @return the set of keywords
     */
    Set<String> getKeywords();

    /**
     * Returns the sort of this keyword.
     *
     * @return the keyword sort. May be null if the keyword does not belong to a
     *         sort.
     */
    IKeywordSort getSort();

    /**
     * Returns the description for this keyword. The description may be null to
     * indicate that no description is available.
     *
     * @return the description for the keyword
     */
    String getDescription();

    /**
     * Creates a new parser for this keyword. Creating a new object allows to
     * keep a state in the parser. A parser created with this method must only
     * be used once. But implementations of this interface may return the same
     * object for each call, if no state is required.
     *
     * @return the parser for parsing text after this keyword
     */
    IKeywordParser createParser();

    /**
     * Creates a new {@link IKeywordAutoProposer} which makes proposals for the
     * content of this keyword.
     *
     * @return an {@link IKeywordAutoProposer}
     */
    IKeywordAutoProposer createAutoProposer();

    /**
     * Returns the Keywords specific Validator.
     *
     * @return the Validator or null if there is none.
     */
    IKeywordValidator getKeywordValidator();

}
