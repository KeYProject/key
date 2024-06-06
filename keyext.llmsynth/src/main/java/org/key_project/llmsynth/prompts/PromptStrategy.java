package org.key_project.llmsynth.prompts;

import java.util.Iterator;

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

    public static final Iterable<Prompt> NO_PROMPTS = () -> empty_iterator; // todo: this seems like it's in the wrong place

    public static <TReason extends PromptReason, TUserData> IPromptStrategy<TUserData> getDefault() {
        return (reason, data, newBuilder) -> NO_PROMPTS;
    }

    public static <TReason extends PromptReason, TUserData> IPromptStrategy<TUserData> combine(
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

    public static <TReason extends PromptReason, TUserData> IPromptStrategy<TUserData> registerAlternativeWhenEmpty(
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
