/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

/**
 * The interface Matcher models a predicate which allows to match tokens of a type.
 * 
 * The class {@link SequenceRule} has a sequence of token options against which
 * the input stream is matched. This sequence is made up of {@link Matcher}
 * objects.
 * 
 * A simple matcher for strings which checks for equality would be:
 * 
 * <pre>
 * class EqMatcher implements Matcher&lt;String&gt; {
 *     String expect;
 * 
 *     public EqMatcher(String string) {
 *         expect = string;
 *     }
 * 
 *     &#064;Override
 *     public boolean matches(String t) {
 *         return expect.equals(t);
 *     }
 * }
 * </pre>
 * 
 * A matcher which allows for either tokens (of some unknown class Token) with id 42 or
 * whose content is "42":
 * <pre>
 * class SomeMatcher implements Matcher&lt;Token&gt; {
 *     &#064;Override
 *     public boolean matches(Token t) {
 *         return t.id == 42 || "42".equals(t.content);
 *     }
 * }
 * </pre>
 * 
 * @author mattias ulbrich
 */
public interface Matcher<T> {

    /**
     * Checks whether a token matches fulfils some condition.
     * 
     * @param token
     *            the token to check.
     * 
     * @return true, if successful
     */
    boolean matches(T token);

}
