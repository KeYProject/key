/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

import org.jspecify.annotations.NonNull;

import java.util.List;

/*
 * def expression(rbp=0):
 global token
 t = token
 token = next()
 left = t.nud()
 while rbp < token.lbp:
 t = token
 token = next()
 left = t.led(left)

 return left
 */

/**
 * A MixFixParser allows to parse arbitrary <i>operator grammars</i> with
 * rule-based precedences even if they are ambiguous.
 *
 * Top down recursive descent is used to parse a stream of tokens.
 *
 * The set of rules is given dynamically (at runtime) by an instance of
 * {@link MixFixRuleCollection}.
 *
 * A grammar is called is called operator grammar if in no right hand side of a
 * production two consequent non-terminal symbols appear. A grammar is called a
 * (per-terminal) precedence grammar if certain relations on the terminal
 * symbols can be established which allows easy parsing. This is the case for
 * most expression grammars. We aim for more generality and allow therefore
 * rules with different precedences for one symbol.
 *
 * The runtime performance of this system is theoretically poor since the
 * backtracking implies an exponential runtime. In reality, however, only very
 * little is backtracked.
 *
 * The rules are instances of the interface {@link MixFixRule}. They are called
 * using the method {@link MixFixRule#parse(ParseContext, int)} to return a
 * value of the result type.
 *
 * Simple rules (especially identifiers and some built-in rules) will directly
 * implement the rule interface. Most compound rules for operators can extends
 * {@link SequenceRule} however.
 *
 * <h3>Further reading</h3>
 * <ol>
 * <li>Wieland, Jacob. <i>Parsing Mixfix Expressions.
 * Dealing with User-Defined Mixfix Operators Efficiently<i></li>
 * <li>http://effbot.org/zone/simple-top-down-parsing.htm</li>
 * </ol>
 *
 * <h3>Remarks</h3>
 * NUD is short for null denotation, LED for left denotation.
 *
 * @param R
 *            the result type of the parsing process.
 *
 * @param T
 *            the type of the tokens to be used for parsing.
 *
 * @author mattias ulbrich
 *
 */
public class MixFixParser<R, T> {

    /**
     * The collection of rules to be used.
     */
    private final MixFixRuleCollection<R, T> rules;

    /**
     * Instantiates a new mix fix parser.
     *
     * @param rules
     *            the rules collection
     */
    public MixFixParser(MixFixRuleCollection<R, T> rules) {
        super();
        this.rules = rules;
    }

    /**
     * Parses an expression from a stream of tokens.
     *
     * The parser can be used to parse more than one stream (even at the same
     * time).
     *
     * @param tokenStream
     *            the token stream to examine.
     *
     * @return the resulting object.
     *
     * @throws MixFixException
     *             in case of syntax errors
     */
    public R parseExpression(List<T> tokenStream) throws MixFixException {

        if (tokenStream.isEmpty()) {
            throw new MixFixException("Empty token stream");
        }

        MaxList<T> tokenMaxStream = new MaxList<T>(tokenStream);
        ParseContext<R, T> context = new ParseContext<R, T>(this,
                tokenMaxStream);
        ADTList<ParseContext<R, T>> results = parseExpression(context, 0);

        if (results.isEmpty()) {
            int max = tokenMaxStream.getMaxReadIndex();
            T token = null;
            if(max != -1) {
                token = tokenMaxStream.get(max);
            }
		// TODO toekn may be null
            throw new MixFixException("Syntax error near " + token, token);
        }

        ParseContext<R, T> goodResult = null;
        int maxPos = 0;

        // System.out.println(results);

        for (ParseContext<R, T> ctx : results) {
            if (ctx.hasFinished()) {
                if (goodResult == null) {
                    goodResult = ctx;
                } else {
                    throw new MixFixException(
                            "Ambiguous parse results. Two results are:\n"
                                    + goodResult.getResult() + ",\n"
                                    + ctx.getResult(), tokenStream.get(0));
                }
            }
            maxPos = Math.max(maxPos, ctx.getCurrentPosition());
        }

        if (goodResult == null) {
            int max = tokenMaxStream.getMaxReadIndex();
            T token = tokenMaxStream.get(max);
            throw new MixFixException("Syntax error near " + token, token);
        }

        return goodResult.getResult();
    }

    /**
     * Parses an expression which has a minimum left binding.
     *
     * The method is package visible to allow for call backs from
     * {@link ParseContext}.
     *
     * This is the point were NUD-rules are queried.
     *
     * @param context
     *            the context to use
     * @param minBinding
     *            the minimum left binding for the first operator
     *
     * @return a list of contexts to proceed with
     */
    ADTList<ParseContext<R, T>> parseExpression(@NonNull ParseContext<R, T> context, int minBinding) {

        DebugLog.enter(context, minBinding);
        ADTList<ParseContext<R, T>> result = ADTList.nil();

        // Bugfix: The max binding needs to be removed here
        context = context.resetMaxBinding();

        List<MixFixRule<R, T>> nudRules = rules.getNUDRules();
        for (MixFixRule<R, T> rule : nudRules) {
            ADTList<ParseContext<R, T>> resultCtxs = rule.parse(context,
                    minBinding);
            for (ParseContext<R, T> resultCtx : resultCtxs) {
                result = result.consAll(continueParsing(resultCtx, minBinding));
            }
        }

        DebugLog.leave(result);
        return result;
    }

    /**
     * Continue parsing with a left-recursive rule.
     *
     * This is the point were LED-rules are queried.
     *
     * @param context
     *            the context to use
     * @param minBinding
     *            the minimum left binding for the first operator
     *
     * @return a list of contexts to proceed with
     */
    private ADTList<ParseContext<R, T>> continueParsing(
            @NonNull ParseContext<R, T> context, int minBinding) {

        DebugLog.enter(context, minBinding);
        ADTList<ParseContext<R, T>> result = ADTList.singleton(context);

        // end of input -> return the given context, which is valid
        if (context.hasFinished()) {
            DebugLog.leave(result);
            return result;
        }

        // check all possible led rules if they match
        List<MixFixRule<R, T>> ledRules = rules.getLEDRules();
        for (MixFixRule<R, T> rule : ledRules) {
            ADTList<ParseContext<R, T>> resultCtxs = rule.parse(context,
                    minBinding);
            for (ParseContext<R, T> resultCtx : resultCtxs) {
                // TODO should this not be resultCtx.getLastBinding?
                result = result.consAll(continueParsing(resultCtx, minBinding));
            }
        }

        DebugLog.leave(result);
        return result;
    }

}
