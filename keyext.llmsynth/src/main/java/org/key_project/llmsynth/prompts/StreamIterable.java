package org.key_project.llmsynth.prompts;

import java.util.stream.Stream;

public class StreamIterable
{
    public static <T> Stream<T> from(Iterable<T> iterable) {
        return java.util.stream.StreamSupport.stream(iterable.spliterator(), false);
    }

}
