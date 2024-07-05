package org.key_project.llmsynth.prompts;

import java.util.Iterator;

/**
 * Provides static helper methods for interfaces of IPromptStrategy
 */
public final class PromptStrategy
{
    private PromptStrategy() {}

    private static final Iterator<Prompt> empty_iterator = new Iterator<>() {
        @Override
        public boolean hasNext() {
            return false;
        }

        @Override
        public Prompt next() {
            return null;
        }
    };

    /**
     * An iterable containing no values.
     */
    public static final Iterable<Prompt> NO_PROMPTS = () -> empty_iterator; // todo: this seems like it's in the wrong place

    /**
     * Default strategy
     * @return A prompt strategy that returns no prompt on any input
     * @param <TUserData> user data
     */
    public static <TUserData> IPromptStrategy<TUserData> getDefault() {
        return (reason, data, newBuilder) -> NO_PROMPTS;
    }

    /**
     *
     * @param left The first strategy to use
     * @param right The second strategy to use
     * @return A new prompt strategy that applies both given strategies and concatenates their results.
     * @param <TUserData> user data
     */
    public static <TUserData> IPromptStrategy<TUserData> combine(
            IPromptStrategy<TUserData> left,
            IPromptStrategy<TUserData> right) {
        return (reason, data, newBuilder) -> {
            var lit = left.apply(reason, data, newBuilder);
            var rit = right.apply(reason, data, newBuilder);
            // This would be much easier, when using ApacheCommons iterator chain
            return () -> new Iterator<>() {
                Iterator<Prompt> current = lit.iterator();
                Iterator<Prompt> next = rit.iterator();

                @Override
                public boolean hasNext() {
                    return current.hasNext();
                }

                @Override
                public Prompt next() {
                    var val = current.next();
                    if (!current.hasNext() && next != null) {
                        current = next;
                        next = null;
                    }
                    return val;
                }
            };
        };
    }

    /**
     *
     * @param defaultStrategy The strategy to usually use
     * @param fallbackStrategy The backup strategy
     * @return A strategy that applies only the defaultStrategy. If however the first strategy yields an empty iterable, then the fallback is applied
     * @param <TUserData> user data
     */
    public static <TUserData> IPromptStrategy<TUserData> registerAlternativeWhenEmpty(
            IPromptStrategy<TUserData> defaultStrategy,
            IPromptStrategy<TUserData> fallbackStrategy) {
        return (r, d, b) -> {
            var res = defaultStrategy.apply(r, d, b);
            if (res.iterator().hasNext()) {
                return res;
            } else {
                return fallbackStrategy.apply(r, d, b);
            }
        };
    }
}
