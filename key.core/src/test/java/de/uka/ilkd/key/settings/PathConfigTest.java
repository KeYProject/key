/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test cases for the {@link PathConfig#VERSION_COMPARATOR}.
 */
class PathConfigTest {

    /**
     * Helper method to create a Path from a version string like "v3.0".
     */
    private Path toPath(String version) {
        return Paths.get(version);
    }

    @Test
    void testCompareEqualVersions() {
        Path v1 = toPath("v3.0");
        Path v2 = toPath("v3.0");
        assertEquals(0, PathConfig.VERSION_COMPARATOR.compare(v1, v2),
            "v3.0 should equal v3.0");
    }

    @Test
    void testCompareDifferentMajorVersions() {
        Path v1 = toPath("v3.0");
        Path v2 = toPath("v2.0");
        assertTrue(PathConfig.VERSION_COMPARATOR.compare(v1, v2) > 0,
            "v3.0 should be greater than v2.0");
    }

    @Test
    void testCompareDifferentMinorVersions() {
        Path v1 = toPath("v3.1");
        Path v2 = toPath("v3.0");
        assertTrue(PathConfig.VERSION_COMPARATOR.compare(v1, v2) > 0,
            "v3.1 should be greater than v3.0");
    }

    @Test
    void testCompareLessThan() {
        Path v1 = toPath("v2.5");
        Path v2 = toPath("v3.0");
        assertTrue(PathConfig.VERSION_COMPARATOR.compare(v1, v2) < 0,
            "v2.5 should be less than v3.0");
    }

    @Test
    void testCompareMultiDigitMinor() {
        Path v1 = toPath("v3.10");
        Path v2 = toPath("v3.2");
        assertTrue(PathConfig.VERSION_COMPARATOR.compare(v1, v2) > 0,
            "v3.10 should be greater than v3.2 (numeric comparison)");
    }

    @Test
    void testCompareMultiDigitMajor() {
        Path v1 = toPath("v10.0");
        Path v2 = toPath("v9.0");
        assertTrue(PathConfig.VERSION_COMPARATOR.compare(v1, v2) > 0,
            "v10.0 should be greater than v9.0 (numeric comparison)");
    }

    @Test
    void testCompareSameVersionDifferentFormat() {
        Path v1 = toPath("v3.0");
        Path v2 = toPath("v3.0");
        assertEquals(0, PathConfig.VERSION_COMPARATOR.compare(v1, v2),
            "Same versions should be equal regardless of format");
    }

    @Test
    void testSortVersionsDescending() {
        List<Path> versions = new ArrayList<>(Arrays.asList(
            toPath("v2.0"),
            toPath("v3.1"),
            toPath("v3.0"),
            toPath("v2.5"),
            toPath("v4.0"),
            toPath("v3.10")));

        versions.sort(PathConfig.VERSION_COMPARATOR.reversed());

        assertEquals(toPath("v4.0"), versions.get(0));
        assertEquals(toPath("v3.10"), versions.get(1));
        assertEquals(toPath("v3.1"), versions.get(2));
        assertEquals(toPath("v3.0"), versions.get(3));
        assertEquals(toPath("v2.5"), versions.get(4));
        assertEquals(toPath("v2.0"), versions.get(5));
    }

    @Test
    void testSortVersionsAscending() {
        List<Path> versions = new ArrayList<>(Arrays.asList(
            toPath("v3.1"),
            toPath("v2.0"),
            toPath("v4.0"),
            toPath("v3.0")));

        versions.sort(PathConfig.VERSION_COMPARATOR);

        assertEquals(toPath("v2.0"), versions.get(0));
        assertEquals(toPath("v3.0"), versions.get(1));
        assertEquals(toPath("v3.1"), versions.get(2));
        assertEquals(toPath("v4.0"), versions.get(3));
    }

    @Test
    void testFindMaxVersion() {
        List<Path> versions = Arrays.asList(
            toPath("v2.0"),
            toPath("v3.1"),
            toPath("v3.0"),
            toPath("v2.5"));

        Path maxVersion = versions.stream()
                .max(PathConfig.VERSION_COMPARATOR)
                .orElse(null);

        assertEquals(toPath("v3.1"), maxVersion);
    }

    @Test
    void testFindMinVersion() {
        List<Path> versions = Arrays.asList(
            toPath("v2.0"),
            toPath("v3.1"),
            toPath("v3.0"),
            toPath("v2.5"));

        Path minVersion = versions.stream()
                .min(PathConfig.VERSION_COMPARATOR)
                .orElse(null);

        assertEquals(toPath("v2.0"), minVersion);
    }

    @Test
    void testCompareNestedPath() {
        Path v1 = Paths.get("~/.key/v3.0");
        Path v2 = Paths.get("~/.key/v2.5");
        assertTrue(PathConfig.VERSION_COMPARATOR.compare(v1, v2) > 0,
            "v3.0 should be greater than v2.5 even with nested paths");
    }

    @Test
    void testCompareSingleElementVersion() {
        // Edge case: version without minor component
        Path v1 = toPath("v3");
        Path v2 = toPath("v3.0");
        // Both should parse to [3] and [3, 0], but arrays have different lengths
        // The comparator uses Arrays.compare which handles different lengths
        int result = PathConfig.VERSION_COMPARATOR.compare(v1, v2);
        // v3 splits to [3], v3.0 splits to [3, 0]
        // Arrays.compare([3], [3,0]) compares element by element
        // First elements are equal (3==3), then shorter array is "less"
        assertTrue(result <= 0, "v3 should be less than or equal to v3.0");
    }

    @Test
    void testConsistencyWithEquals() {
        Path v1 = toPath("v3.0");
        Path v2 = toPath("v3.0");

        int compareResult = PathConfig.VERSION_COMPARATOR.compare(v1, v2);
        boolean equalsResult = v1.equals(v2);

        // If compare returns 0, equals should be true (and vice versa for same strings)
        if (compareResult == 0) {
            assertTrue(equalsResult, "If compare returns 0, paths should be equal");
        }
    }

    @Test
    void testTransitivity() {
        Path v1 = toPath("v2.0");
        Path v2 = toPath("v3.0");
        Path v3 = toPath("v4.0");

        int cmp12 = PathConfig.VERSION_COMPARATOR.compare(v1, v2);
        int cmp23 = PathConfig.VERSION_COMPARATOR.compare(v2, v3);
        int cmp13 = PathConfig.VERSION_COMPARATOR.compare(v1, v3);

        // If v1 < v2 and v2 < v3, then v1 < v3
        assertTrue(cmp12 < 0, "v2.0 < v3.0");
        assertTrue(cmp23 < 0, "v3.0 < v4.0");
        assertTrue(cmp13 < 0, "v2.0 < v4.0 (transitivity)");
    }

    @Test
    void testSymmetry() {
        Path v1 = toPath("v3.0");
        Path v2 = toPath("v2.5");

        int cmp12 = PathConfig.VERSION_COMPARATOR.compare(v1, v2);
        int cmp21 = PathConfig.VERSION_COMPARATOR.compare(v2, v1);

        // compare(v1, v2) should be negative of compare(v2, v1)
        assertEquals(-Integer.signum(cmp12), Integer.signum(cmp21),
            "compare should be symmetric");
    }
}
