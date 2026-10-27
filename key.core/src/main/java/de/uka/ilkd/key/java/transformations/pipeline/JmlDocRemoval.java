/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.regex.Pattern;

import de.uka.ilkd.key.java.transformations.MarkerStatementHelper;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.jml.doc.*;
import org.jspecify.annotations.NonNull;

/**
 * Removes leftover raw JML comments that JMLtk could not turn into typed JML AST nodes.
 * <p>
 * With {@code processJml} and {@code keepJmlDocs} enabled, every JML comment becomes a typed
 * node unless parsing fails; failing class level comments stay attached as
 * {@link JmlDocContainer}s ({@link JmlDocType}, {@link JmlDocDeclaration}) and failing method
 * level comments as {@link JmlDocStmt}. Those leftovers are removed here.
 * <p>
 * Most leftovers are harmless/accepted drops ("deprecated crap"), but a {@code name "..."}
 * clause is not: JMLtk cannot parse it, and since the whole spec case containing it is then
 * dropped, the contract would silently lose its name. Such leftovers are therefore rejected
 * loudly instead of being erased.
 *
 * @author Alexander Weigl
 * @version 1 (3/3/26)
 */
public class JmlDocRemoval extends JavaTransformerAbstract {

    /**
     * Matches an unsupported JML {@code name "..."} clause in leftover raw JML text. The word
     * boundary keeps {@code spec_name "..."} (an accepted drop) from matching.
     */
    private static final Pattern NAME_CLAUSE = Pattern.compile("\\bname\\s+\"");

    public JmlDocRemoval(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(it -> {
            if (it instanceof Modifier m) {
                if (m.keyword() instanceof JmlDocModifier) {
                    it.remove();
                }
            }

            if (it instanceof JmlDocContainer container) {
                for (JmlDoc doc : container.getJmlComments()) {
                    if (NAME_CLAUSE.matcher(doc.getContent()).find()) {
                        throw new IllegalArgumentException(
                            "JML `name \"...\"` clauses cannot be parsed by JMLtk; the "
                                + "specification containing them would silently be dropped. "
                                + "Remove the name clause or express it differently: "
                                + doc.getContent());
                    }
                }
            }

            if (it instanceof JmlDocStmt docStmt) {
                // Leftovers re-parsed by the JMLTransformer fallback (merge points, proof
                // scripts, ...) are kept; the JP2KeYConverter translates them. Untouched
                // leftovers are plain drops.
                if (!docStmt.containsData(MarkerStatementHelper.KEY_JML_FALLBACK)) {
                    it.remove();
                }
            } else if (it instanceof JmlDocType || it instanceof JmlDocDeclaration) {
                it.remove();
            }
        });
    }
}
