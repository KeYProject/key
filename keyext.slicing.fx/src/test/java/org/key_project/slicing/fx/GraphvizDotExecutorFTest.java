/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx;

import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.fx.ui.GraphvizDotExecutorF;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless unit test of the non-Swing DOT renderer {@link GraphvizDotExecutorF} (WP-6): the
 * no-graphviz fallback (unavailable dot executable yields an error result, the documented
 * decision that makes the dialogs fall back to the DOT source text) and — if the graphviz dot
 * binary is installed on the test machine — the real PNG render path. The in-app end-to-end
 * behavior (image dialog, statistics dialog, fixed point) is exercised by the
 * {@code key.fx.verify.slicing} hook.
 */
class GraphvizDotExecutorFTest {

    private static final String SAMPLE_DOT = "digraph g { a -> b; }";

    @AfterEach
    void restoreDotExecutable() {
        // the render tests swap the configured dot executable; restore the default
        SlicingSettingsProvider.getSlicingSettings().setDotExecutable("dot");
    }

    @Test
    void missingDotExecutableYieldsErrorResult() {
        SlicingSettingsProvider.getSlicingSettings()
                .setDotExecutable("key-fx-verify-missing-dot-binary");
        GraphvizDotExecutorF.Result result = GraphvizDotExecutorF.renderPng(SAMPLE_DOT);
        assertTrue(result.hasError());
        assertFalse(result.hasImage());
        assertFalse(result.isPng());
    }

    @Test
    void rendersPngWhenGraphvizInstalled() {
        if (!GraphvizDotExecutorF.isDotInstalled()) {
            // documented fallback environment: without graphviz only the error path is
            // verifiable (the verify hook asserts the same two branches in-app)
            SlicingSettingsProvider.getSlicingSettings()
                    .setDotExecutable("key-fx-verify-missing-dot-binary");
            GraphvizDotExecutorF.Result result = GraphvizDotExecutorF.renderPng(SAMPLE_DOT);
            assertTrue(result.hasError());
            return;
        }
        GraphvizDotExecutorF.Result result = GraphvizDotExecutorF.renderPng(SAMPLE_DOT);
        assertTrue(result.hasImage());
        assertTrue(result.isPng());
        assertFalse(result.hasError());
    }
}
