/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT for details.
 */

package edu.kit.kastel.formal.mixfix;

// TODO Finish Javadoc

import org.jspecify.annotations.NonNull;

/**
 * The Class SequenceRule.
 */
public abstract class SequenceRule<R, T> implements MixFixRule<R, T> {

    /**
     * The sequence.
     */
    private final Matcher<T>[] sequence;

    /**
     * The left binding.
     */
    private final int leftBinding;

    /**
     * The right binding.
     */
    private final int rightBinding;

    /**
     * Instantiates a new sequence rule.
     *
     * <p>
     * Please note that the array is not deep copied and that you should
     * <b>not</b> change it after the invocation of this constructor
     *
     * @param sequence
     *            the sequence
     * @param leftBinding
     *            the left binding
     * @param rightBinding
     *            the right binding
     */
    protected SequenceRule(Matcher<T>[] sequence, int leftBinding, int rightBinding) {
        super();
        this.sequence = sequence;
        this.leftBinding = leftBinding;
        this.rightBinding = rightBinding;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.iti.mixfix.MixFixRule#getLeftBinding()
     */
    /**
     * Gets the left binding.
     *
     * @return the left binding
     */
    public int getLeftBinding() {
        return leftBinding;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.iti.mixfix.MixFixRule#getRightBinding()
     */
    /**
     * Gets the right binding.
     *
     * @return the right binding
     */
    public int getRightBinding() {
        return rightBinding;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.iti.mixfix.MixFixRule#isLeftRecursive()
     */@Override
    public boolean isLeftRecursive() {
        return sequence[0] == null;
    }

    private boolean isRightRecursive() {
        return sequence[sequence.length - 1] == null;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.iti.mixfix.MixFixRule#parse(de.uka.iti.mixfix.ParseContext)
     */
    @Override
    public ADTList<ParseContext<R, T>> parse(@NonNull ParseContext<R, T> context, int minBinding) {

        DebugLog.enter(this, context, minBinding);

        ADTList<R> results = ADTList.nil();
        int origMaxBinding = context.getMaxBinding();

        if (isLeftRecursive()) {

            if (getLeftBinding() > context.getMaxBinding()
                    || getLeftBinding() < minBinding) {
                DebugLog.leave(ADTList.nil());
                return ADTList.nil();
            }

            results = results.cons(context.getResult());
            ADTList<ParseContext<R, T>> returnValue = continueParsing(context, 1, results, origMaxBinding);
            DebugLog.leave(returnValue);
            return returnValue;
        } else {
            ADTList<ParseContext<R, T>> returnValue = continueParsing(context, 0, results, origMaxBinding);
            DebugLog.leave(returnValue);
            return returnValue;
        }
    }

    /**
     * Continue parsing.
     *
     * @param context
     *            the context
     * @param seqPos
     *            the seq pos
     * @param results
     *            the results
     * @param origMaxBinding
     *
     * @return the aDT list< parse context< r, t>>
     */
    private ADTList<ParseContext<R, T>> continueParsing(
            @NonNull ParseContext<R, T> context, int seqPos,
            @NonNull ADTList<R> results, int origMaxBinding) {

        DebugLog.enter(this, context, seqPos, results);

        // consume the non-placeholder positions of the rule
        while (seqPos < sequence.length && sequence[seqPos] != null && !context.hasFinished()) {
            if (!sequence[seqPos].matches(context.getCurrentToken())) {
                DebugLog.leave(ADTList.nil());
                return ADTList.nil();
            }

            context = context.consumeToken();
            seqPos++;
        }

        if (seqPos < sequence.length) {

            // TODO To have fewer ambiguous grammars: Allow for "inner bindings" to use here.
            // Then: minBinding = getPositionBinding(seqPos) + 1 (essentially)
            int minBinding = 0;
            if (seqPos == sequence.length - 1 && isRightRecursive()) {
                // use right binding only in last position if that is nonterminal
                minBinding = getRightBinding()+1;
            }


            if(context.hasFinished()) {
                DebugLog.leave("[]");
                return ADTList.nil();
            }

            ADTList<ParseContext<R, T>> resultCtxs = ADTList.nil();
            ADTList<ParseContext<R, T>> parseRes = context
                    .parseExpression(minBinding);

            for (ParseContext<R, T> parseContext : parseRes) {
                ADTList<R> newRes = results.cons(parseContext.getResult());
                resultCtxs = resultCtxs.consAll(continueParsing(parseContext,
                        seqPos + 1, newRes, origMaxBinding));
            }

            DebugLog.leave(resultCtxs);
            return resultCtxs;

        } else {

            R r = makeResult(results.rev());
            context = context.setResult(r);
            if(isRightRecursive()) {
                context = context.setMaxBinding(
                        Math.min(getRightBinding(), context.getMaxBinding()));
            } else {
                context = context.setMaxBinding(origMaxBinding);
            }
            DebugLog.leave(context);
            return ADTList.singleton(context);

        }

    }

    /**
     * Make result.
     *
     * @param results
     *            the results
     *
     * @return the r
     */
    protected abstract R makeResult(@NonNull ADTList<R> results);

}
