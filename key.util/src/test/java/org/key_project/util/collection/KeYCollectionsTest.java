package org.key_project.util.collection;

import org.junit.jupiter.api.Test;

import java.lang.constant.Constable;
import java.util.List;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.function.Consumer;
import java.util.stream.StreamSupport;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.key_project.util.collection.KeYCollections.runLengthDecoding;
import static org.key_project.util.collection.KeYCollections.runLengthEncoding;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
class KeYCollectionsTest {

    @Test
    void runLengthEncoding_test() {
        assertArrayEquals(new int[]{1, -5, 2, 1}, runLengthEncoding(new int[]{1, 2, 2, 2, 2, 2, 1}));
        assertArrayEquals(new int[]{-5, 2}, runLengthEncoding(new int[]{2, 2, 2, 2, 2}));
        assertArrayEquals(new int[]{}, runLengthEncoding(new int[]{}));
        assertArrayEquals(new int[]{-5, 2, -5, 1}, runLengthEncoding(new int[]{2, 2, 2, 2, 2, 1, 1, 1, 1, 1}));
    }

    @Test
    void runLengthEncoding_test2() {
        assertArrayEquals(new int[]{}, runLengthEncoding(List.of()));
        assertArrayEquals(new int[]{1, -5, 2, 1}, runLengthEncoding(List.of(1, 2, 2, 2, 2, 2, 1)));
        assertArrayEquals(new int[]{-5, 2}, runLengthEncoding(List.of(2, 2, 2, 2, 2)));
        assertArrayEquals(new int[]{-5, 2, -5, 1}, runLengthEncoding(List.of(2, 2, 2, 2, 2, 1, 1, 1, 1, 1)));
    }


    @Test
    void runLengthDecoding_test() {
        Consumer<int[]> tester = original -> {
            final var rle = runLengthEncoding(original);
            final var iter = runLengthDecoding(rle);
            var stream = StreamSupport.stream(Spliterators.spliteratorUnknownSize(iter, Spliterator.ORDERED), false)
                    .mapToInt(it -> it)
                    .toArray();
            System.out.println(stream);
            assertArrayEquals(original, stream);
        };
        tester.accept(new int[]{1, 2, 2, 2, 2, 2, 1});
        tester.accept(new int[]{2, 2, 2, 2, 2});
        tester.accept(new int[]{});
        tester.accept(new int[]{2, 2, 2, 2, 2, 1, 1, 1, 1, 1});
    }


}
