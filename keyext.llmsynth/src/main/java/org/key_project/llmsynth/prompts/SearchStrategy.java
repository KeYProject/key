package org.key_project.llmsynth.prompts;

import org.key_project.llmsynth.SearchNode;

import java.util.Iterator;

/**
 * Provides static helper methods for interfaces of IPromptStrategy
 */
public final class SearchStrategy
{
    private SearchStrategy() {}

    private static <T> Iterator<SearchNode<T>> getEmptyIterator() {
        return new Iterator<>() {
            @Override
            public boolean hasNext() {
                return false;
            }

            @Override
            public SearchNode<T> next() {
                return null;
            }
        };
    }

    /**
     * An iterable containing no values.
     */
    public static <T> Iterable<SearchNode<T>>  empty() {
        return SearchStrategy::getEmptyIterator;
    }; // todo: this seems like it's in the wrong place

    /**
     * Default strategy
     * @return A prompt strategy that returns no prompt on any input
     * @param <TUserData> user data
     */
    public static <TUserData> ISearchStrategy<TUserData> getDefault() {
        Iterator<SearchNode<TUserData>> it = getEmptyIterator();
        return (node, newBuilder) -> empty();
    }

    /**
     *
     * @param left The first strategy to use
     * @param right The second strategy to use
     * @return A new prompt strategy that applies both given strategies and concatenates their results.
     * @param <TUserData> user data
     */
    public static <TUserData> ISearchStrategy<TUserData> combine(
            ISearchStrategy<TUserData> left,
            ISearchStrategy<TUserData> right) {
        return (node, newBuilder) -> {
            var lit = left.apply(node, newBuilder);
            var rit = right.apply(node, newBuilder);
            // This would be much easier, when using ApacheCommons iterator chain
            return () -> new Iterator<>() {
                Iterator<SearchNode<TUserData>> current = lit.iterator();
                Iterator<SearchNode<TUserData>> next = rit.iterator();

                @Override
                public boolean hasNext() {
                    return current.hasNext();
                }

                @Override
                public SearchNode<TUserData> next() {
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
    public static <TUserData> ISearchStrategy<TUserData> registerAlternativeWhenEmpty(
            ISearchStrategy<TUserData> defaultStrategy,
            ISearchStrategy<TUserData> fallbackStrategy) {
        return (n, b) -> {
            var res = defaultStrategy.apply(n, b);
            if (res.iterator().hasNext()) {
                return res;
            } else {
                return fallbackStrategy.apply(n, b);
            }
        };
    }
}
