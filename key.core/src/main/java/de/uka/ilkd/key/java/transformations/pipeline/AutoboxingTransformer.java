/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Pipeline step that desugars Java boxing and unboxing conversions.
 * <p>
 * Boxing becomes {@link java.lang.Integer#valueOf(int)}-style calls; unboxing becomes a read of
 * the wrapper's {@code value} field, which gives the same happy-path/null-obligation split as an
 * ordinary field access. See {@link AutoboxingRewriter} for the conversion rules.
 */
public final class AutoboxingTransformer implements JavaTransformer {
    private static final Logger LOGGER = LoggerFactory.getLogger(AutoboxingTransformer.class);

    private final AutoboxingRewriter rewriter = new AutoboxingRewriter();

    @Override
    public void apply(CompilationUnit cu) {
        LOGGER.debug("Rewriting boxing conversions in {}", cu.getStorage());
        rewriter.rewrite(cu);
    }
}
