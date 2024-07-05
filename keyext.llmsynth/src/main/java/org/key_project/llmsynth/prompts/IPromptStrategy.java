package org.key_project.llmsynth.prompts;

import java.util.function.Supplier;

/**
 * The main interface used to complete a benchmark.
 * Given A reason to prompt an oracle it shall provide possible prompts that may yield a solution to the problem described in the benchmark.
 * @param <TUserData> user data
 */
public interface IPromptStrategy<TUserData> {
    // TODO: think about having LLM specific PromptRequestBuilders (if PRB is right type then apply else fallback - with the 'last' fallback just throwing an error)
    Iterable<Prompt> apply(PromptReason reason, TUserData data, Supplier<PromptBuilder> newBuilder);

//    default IPromptStrategy<TReason, TUserData> withFallback(IPromptStrategy<TReason, TUserData> fallback) {
//        return (r, d, b) -> {
//            try {
//                return apply(r, d, b);
//            } catch (UnsupportedOperationException e) { // TODO: perhaps a custom runtime exception here
//                return fallback.apply(r, d, b);
//            }
//        };
//    }

    /**
     * Syntactic sugar
     * @param other the alternative
     * @return PromptStrategy.registerAlternativeWhenEmpty(self, other)
     */
    default IPromptStrategy<TUserData> orElse(IPromptStrategy<TUserData> other) {
        return PromptStrategy.registerAlternativeWhenEmpty(this, other);
    }

    /**
     * Syntactic sugar
     * @param other the strategy to be used after
     * @return PromptStrategy.combine(self, other)
     */
    default IPromptStrategy<TUserData> combine(IPromptStrategy<TUserData> other) {
        return PromptStrategy.combine(this, other);
    }

    // The class parameter is required, as Java generics do _not_ allow for instanceof checks through a mere generic parameter
    // This is because _all_ generic information is gone at runtime, as if the generic parameter was just of type "Object"
    // This includes instanceof checks. As the type isn't known (and not stored via compiler sugar) this one of the few work-arounds.
//    default IPromptStrategy<PromptReason, TUserData> broaden(Class<TReason> type) {
//        return (r, d, b) -> {
//            if (type.isInstance(r)) {
//                return apply(type.cast(r), d, b);
//            } else {
//                return PromptStrategy.NO_PROMPTS;
//            }
//        };
//    }
}
