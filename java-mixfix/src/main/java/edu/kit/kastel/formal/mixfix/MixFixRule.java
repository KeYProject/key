/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

public interface MixFixRule<R, T> {

    /**
     * Determines the type of the rule.
     *
     * <p>
     * A rule is left recursive iff its representation as a production starts
     * with a non-terminal.
     *
     * <p>
     * <i>Or equivalently</i>: A rule is left recursive iff it is used in a left
     * denotation context (see {@link MixFixRuleCollection}).
     *
     * @return <code>true</code> iff this rule is left recursive
     */
    public boolean isLeftRecursive();

    /**
     * Continues parsing with this rule in a given context.
     *
     * <p>
     * If this rule is left recursive you can retrieve the result of the
     * recursion using {@link ParseContext#getResult()}. The method should
     * return a collection of all possible parsing contexts in which this rule
     * can finish on the given input context. This is the empty list if this
     * rule cannot be applied in the context. It can return more than one
     * context if the grammar is ambiguous.
     *
     * <p>
     * If the (left-)binding of the first terminal of this rule is
     * <dl>
     * <dt>less than <code>minBinding</code>,</dt>
     * <dd>the previously encountered terminal binds stronger and this rule
     * cannot be applied (in this context)</dd>
     * <dt>greater than <code>context.getLastBinding()</code></dt>
     * <dd>the result in context is only possible if this rule cannot will not
     * be applied (in this context)</dd>
     * </dl>
     * In both cases, an implementing method must return {@link ADTList#nil()}
     *
     * @param context
     *            the context to use
     * @param minBinding
     *            the minimum left binding for the first operator
     *
     * @return a non-null (possibly empty) list of parse-contexts.
     */
    public ADTList<ParseContext<R, T>> parse(ParseContext<R, T> context, int minBinding);

}